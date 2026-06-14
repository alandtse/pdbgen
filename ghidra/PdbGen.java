//Generates a PDB containing public symbols and type information derived from ghidra's database
//@author Brett Wandel
//@category Windows
//@keybinding ctrl G
//@menupath Tools.Generate PDB
//@toolbar

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.time.Duration;
import java.time.Instant;
import java.util.UUID;
import java.util.concurrent.TimeUnit;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

import org.apache.commons.io.FilenameUtils;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import generic.util.Path;
import ghidra.app.script.GhidraScript;
import ghidra.app.services.ConsoleService;
import ghidra.program.model.address.Address;
import ghidra.program.model.data.*;
import ghidra.program.model.data.Enum;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionManager;
import ghidra.program.model.listing.FunctionSignature;
import ghidra.program.model.listing.Parameter;
import ghidra.program.model.symbol.Symbol;
import ghidra.program.model.symbol.SymbolType;
import ghidra.util.UniversalID;
import ghidra.util.exception.CancelledException;

public class PdbGen extends GhidraScript {
	// Note: we are manually serializing json here, this is just to avoid any
	// dependencies.
	// this means it will break if we have any fields that need escaping.
	boolean prettyPrint = true;          // output json using pretty print (larger files, easier to debug)
	boolean filterToFunctionTypes = true; // only emit types reachable from function signatures; cuts PDB size significantly
	boolean debug = false;               // log every serialized type to console
	boolean useFallback = false;         // true during Phase 2: substitute placeholders for unresolvable deps
	Map<String, String> typedefs = new HashMap<String, String>();
	Set<String> serialized = new HashSet<String>();  // HashSet for O(1) isSerialized() lookup
	Map<String, String> forwardDeclared = new HashMap<String, String>();
	Map<Integer, String> placeholderTypeIds = new HashMap<Integer, String>(); // size -> type id for fallback fields

	Map<Address, FunctionDefinition> entrypoints = new HashMap<Address, FunctionDefinition>();
	Instant start = Instant.now();
	Instant sectionStart = Instant.now();
	Integer item = 0;
	int sectionItemCount = 0;  // items processed in the current section; reset at each section boundary
	String lastStatus = "";
	Map<String, Duration> sectionTimer = new LinkedHashMap<String, Duration>();
	Map<String, Integer> sectionItems  = new LinkedHashMap<String, Integer>();

	private String timeElapsed() {
		return timeElapsed(start);
	}

	private String timeElapsed(Instant start) {
		Duration duration = Duration.between(start, Instant.now());
		return toString(duration);
	}

	private String toString(Duration duration) {
		long HH = duration.toHours();
		long MM = duration.toMinutesPart();
		long SS = duration.toSecondsPart();
		return String.format("%02d:%02d:%02d", HH, MM, SS);
	}

	private void updateMonitor(String status) throws CancelledException {
		String itemString = "";
		if (!lastStatus.equals(status)) {
			// we're in a new section
			if (!lastStatus.isEmpty()) {
				sectionTimer.put(lastStatus, Duration.between(sectionStart, Instant.now()));
				sectionItems.put(lastStatus, sectionItemCount);
			}
			sectionStart = Instant.now();
			sectionItemCount = 0;
			lastStatus = status;
		}
		if (monitor.isIndeterminate())
			itemString = item.toString();
		monitor.setMessage(String.format("%s/%s: %s %s", timeElapsed(sectionStart), timeElapsed(), status, itemString));
		monitor.checkCancelled();
		monitor.incrementProgress(1);
		item = item + 1;
		sectionItemCount++;
	}

	private void printSectionTimers() throws CancelledException {
		if (!lastStatus.isEmpty()) {
			sectionTimer.put(lastStatus, Duration.between(sectionStart, Instant.now()));
			sectionItems.put(lastStatus, sectionItemCount);
		}
		Duration total = Duration.between(start, Instant.now());
		long totalSec = Math.max(total.toSeconds(), 1); // guard against div-by-zero on fast runs
		int totalItems = 0;
		for (int n : sectionItems.values()) totalItems += n;

		String fmt = "  %-42s%-12s%,10d   %.1f%%\n";
		String fmtTotal = "  %-42s%-12s%,10d\n";
		printf("[PDBGEN] Total Time by Section\n");
		printf("  %-42s%-12s%10s   %s\n", "Phase", "Time", "Items", "%");
		printf("  %s\n", "-".repeat(74));
		for (String s : sectionTimer.keySet()) {
			int items = sectionItems.getOrDefault(s, 0);
			printf(fmt, s, toString(sectionTimer.get(s)), items,
					(float) sectionTimer.get(s).toSeconds() / totalSec * 100);
		}
		printf("  %s\n", "-".repeat(74));
		printf(fmtTotal, "Total", toString(total), totalItems);
	}

	/**
	 * Ghidra's recorded executable path can go stale if the binary is later renamed or moved
	 * (e.g. a game exe gets renamed as it's patched: SkyrimSE.1.7.79.exe -> SkyrimSE.1.7.99.exe,
	 * while Ghidra's project still remembers the old path/name). If the recorded path no longer
	 * exists, resolve it in two steps: first, search its directory for a same-extension file
	 * whose MD5 matches the MD5 Ghidra captured at import time (a confirmed match -- but this
	 * never succeeds for a Steamless-stripped copy, since removing the DRM stub changes the
	 * bytes even when the underlying game build is identical); failing that, fall back to a
	 * same-prefix file in the same directory whose PE VersionInfo.FileVersion matches the
	 * version encoded in the recorded filename (e.g. SkyrimSE.1.7.79.exe -> "1.7.79" must appear
	 * in the candidate's FileVersion) -- VERSIONINFO survives DRM stripping, so this still gives
	 * a real, verified signal instead of guessing off the filename alone. Output naming always
	 * derives from the (possibly stale) recorded path, so concurrent runs against different game
	 * versions keep distinct output filenames.
	 */
	private String resolveExecutablePath(String recordedPath) {
		File recorded = new File(recordedPath);
		if (recorded.exists()) {
			return recordedPath;
		}

		String expectedMd5 = currentProgram.getExecutableMD5();
		File dir = recorded.getParentFile();
		if (expectedMd5 == null || dir == null || !dir.isDirectory()) {
			return null;
		}

		String ext = FilenameUtils.getExtension(recordedPath).toLowerCase();
		File[] candidates = dir.listFiles((d, name) -> ext.isEmpty() || name.toLowerCase().endsWith("." + ext));
		if (candidates == null) {
			return null;
		}

		String match = null;
		for (File candidate : candidates) {
			try {
				if (expectedMd5.equalsIgnoreCase(md5(candidate))) {
					if (match != null) {
						printf("[PDBGEN] WARNING: multiple files match MD5 for stale path '%s': %s and %s -- refusing to guess\n",
								recordedPath, match, candidate);
						return null;
					}
					match = candidate.getAbsolutePath();
				}
			} catch (IOException e) {
				printf("[PDBGEN] WARNING: failed to hash %s: %s\n", candidate, e);
			}
		}

		if (match != null) {
			printf("[PDBGEN] recorded executable path is stale ('%s' no longer exists); resolved actual file by MD5 match: %s\n",
					recordedPath, match);
			return match;
		}

		// Last resort: the recorded filename encodes a game version (e.g. SkyrimSE.1.7.79.exe
		// or SkyrimSE.1170.exe). Look for a same-prefix candidate whose actual PE FileVersion
		// resource contains that version -- unlike a bare filename guess, this is still a real
		// (if weaker than MD5) confirmation, and it works across DRM stripping.
		String baseName = FilenameUtils.getBaseName(recordedPath);
		int firstDot = baseName.indexOf('.');
		if (firstDot < 0) {
			return null;
		}
		String prefix = baseName.substring(0, firstDot);
		String versionToken = baseName.substring(firstDot + 1);

		String versionMatch = null;
		for (File candidate : candidates) {
			if (!candidate.getName().startsWith(prefix)) {
				continue;
			}
			String fileVersion = getFileVersion(candidate);
			if (fileVersion == null || !versionContains(fileVersion, versionToken)) {
				continue;
			}
			if (versionMatch != null) {
				printf("[PDBGEN] WARNING: multiple files match version '%s' for stale path '%s' -- refusing to guess\n",
						versionToken, recordedPath);
				return null;
			}
			versionMatch = candidate.getAbsolutePath();
		}

		if (versionMatch != null) {
			printf("[PDBGEN] no MD5 match for stale path '%s' (expected after Steamless DRM stripping); resolved by FileVersion match ('%s'): %s\n",
					recordedPath, versionToken, versionMatch);
		}
		return versionMatch;
	}

	// Reads the PE VersionInfo.FileVersion of a file via PowerShell, since the JDK has no
	// built-in way to read Win32 file version resources. Returns null on any failure.
	private static String getFileVersion(File file) {
		try {
			String escaped = file.getAbsolutePath().replace("'", "''");
			ProcessBuilder pb = new ProcessBuilder("powershell", "-NoProfile", "-NonInteractive", "-Command",
					"(Get-Item -LiteralPath '" + escaped + "').VersionInfo.FileVersion");
			pb.redirectErrorStream(true);
			Process p = pb.start();
			String line;
			try (BufferedReader r = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
				line = r.readLine();
			}
			p.waitFor(5, TimeUnit.SECONDS);
			return line == null || line.isBlank() ? null : line.trim();
		} catch (Exception e) {
			return null;
		}
	}

	// True if the dot-separated numeric components of `token` (e.g. "1.7.79" or "1170") appear
	// as a contiguous, ordered run within the dot-separated components of `fileVersion`
	// (e.g. "1.7.79.0" or "1.6.1170.0"). Plain substring/digit matching would false-positive
	// across differing naming conventions (dotted SE versions vs bare AE build numbers).
	private static boolean versionContains(String fileVersion, String token) {
		String[] a = token.split("[^0-9]+");
		String[] b = fileVersion.split("[^0-9]+");
		if (a.length == 0 || a.length > b.length) {
			return false;
		}
		outer:
		for (int start = 0; start + a.length <= b.length; start++) {
			for (int i = 0; i < a.length; i++) {
				if (!a[i].equals(b[start + i])) {
					continue outer;
				}
			}
			return true;
		}
		return false;
	}

	private static String md5(File file) throws IOException {
		try {
			MessageDigest digest = MessageDigest.getInstance("MD5");
			try (InputStream in = new java.io.FileInputStream(file)) {
				byte[] buf = new byte[1 << 16];
				int n;
				while ((n = in.read(buf)) > 0) {
					digest.update(buf, 0, n);
				}
			}
			StringBuilder sb = new StringBuilder();
			for (byte b : digest.digest()) {
				sb.append(String.format("%02x", b));
			}
			return sb.toString();
		} catch (NoSuchAlgorithmException e) {
			throw new IOException(e);
		}
	}

	private void printPdbSummary(String pdbPath, JsonObject data) {
		JsonArray types   = data.get("types").getAsJsonArray();
		JsonArray symbols = data.get("symbols").getAsJsonArray();

		int pubFunctions = 0, pubData = 0, gproc = 0;
		for (JsonElement el : symbols) {
			JsonObject sym = el.getAsJsonObject();
			String type = sym.get("type").getAsString();
			if ("S_PUB32".equals(type)) {
				if (sym.has("function") && sym.get("function").getAsBoolean()) pubFunctions++;
				else pubData++;
			} else if ("S_GPROC32".equals(type)) {
				gproc++;
			}
		}

		String sizeStr;
		File pdb = new File(pdbPath);
		if (pdb.exists()) {
			long bytes = pdb.length();
			if (bytes >= 1024L * 1024 * 1024)
				sizeStr = String.format("%.2f GB", bytes / (1024.0 * 1024 * 1024));
			else if (bytes >= 1024 * 1024)
				sizeStr = String.format("%.2f MB", bytes / (1024.0 * 1024));
			else if (bytes >= 1024)
				sizeStr = String.format("%.1f KB", bytes / 1024.0);
			else
				sizeStr = String.format("%d B", bytes);
		} else {
			sizeStr = "not found";
		}

		printf("[PDBGEN] PDB Output Summary\n");
		printf("  %-32s%,d\n",  "Types emitted:",               types.size());
		printf("  %-32s%,d\n",  "Public functions (S_PUB32):",  pubFunctions);
		printf("  %-32s%,d\n",  "Public data (S_PUB32):",       pubData);
		printf("  %-32s%,d\n",  "Full procedures (S_GPROC32):", gproc);
		printf("  %-32s%s\n",   "PDB file size:",               sizeStr);
	}

	private int getSize(DataType dt) {
		int sum = 0;
		if (dt instanceof FunctionDefinition) {
			FunctionDefinition func = (FunctionDefinition) dt;
			for (ParameterDefinition p : func.getArguments()) {
				sum += getSize(p.getDataType());
			}
			return sum;
		}
		if (dt instanceof Array) {
			return dt.getLength();
		}
		if (dt instanceof Union) {
			Union union = (Union) dt;
			for (DataTypeComponent c : union.getComponents()) {
				sum += getSize(c.getDataType());
			}
			return sum;
		}
		if (dt instanceof Enum) {
			Enum enum1 = (Enum) dt;
			return enum1.getValues().length;
		}
		if (dt instanceof Structure) {
			Structure struct = (Structure) dt;
			for (DataTypeComponent c : struct.getComponents()) {
				sum += getSize(c.getDataType());
			}
			return sum;
		}
		return 1;
	}

	private boolean isSerialized(DataType dt) {
		String id = GetId(dt);
		return isSerialized(id);
	}

	private boolean isSerialized(String id) {
		return serialized.contains(id);
	}

	private void setSerialized(DataType dt) {
		String id = GetId(dt);
		serialized.add(id);
	}

	private String GetIdUnmapped(DataType dt) {
		if (dt == null) {
			// Not sure if this should be LF_NULLLEAF (0x0009)
			// using no type (0x0000) first, this might need to change
			return "0x0000"; // uncharacterized type (no type)
		}

		// FML... this needs to be fixed at some point.
		String name = dt.getPathName();
		// if (name.contains("-")) {
		// name = name.split("-")[0];
		// }
		//
		// if (name == "/undefined") {
		// // this should be done as a typedef, but we can't get "/undefined" by path
		// for some reason.
		// return "0x0003";
		// }

		// some BitFieldDataTypes do not have a source archive... no idea why
		SourceArchive source = dt.getSourceArchive();
		if (source != null) {
			name = String.format("%s:%s", dt.getSourceArchive().getName(), name);
		}

		// a BitField does not have a unique name, so we create one
		// The hashCode is based on basetype.hashcode, bitOffset and bitSize...
		// so basetype.name:bitSize:bitOffset should be unique.
		if (dt instanceof BitFieldDataType) {
			name = String.format("%s:%d", name, ((BitFieldDataType) dt).getBitOffset());
		}

		// some types don't have UniversalIDs, so we use the name instead
		return name;
	}

	private String GetId(DataType dt) {
		String key = GetIdUnmapped(dt);

		// follow the typedefs to the original type.
		while (typedefs.containsKey(key)) {
			assert key != typedefs.get(key);
			key = typedefs.get(key);
		}

		return key;
	}

	// Get the new ID for a type that has been forward declared.
	private String GetFwdId(DataType dt) {
		String id = GetId(dt);
		if (!forwardDeclared.containsKey(id)) {
			String alias = UUID.randomUUID().toString();
			forwardDeclared.put(id, alias);
		}
		return forwardDeclared.get(id);
	}

	private List<JsonObject> dump(Pointer x) {
		List<JsonObject> entries = new ArrayList<JsonObject>();
		String referentId;
		if (!isSerialized(x.getDataType())) {
			if (!useFallback) return null;
			DataType referent = x.getDataType();
			if (referent instanceof Structure || referent instanceof Union || referent instanceof Enum) {
				// Emit a named forward declaration so the pointer keeps its type name.
				// Debuggers and RTTI can then reconnect the type by name if its full
				// definition is found later (e.g. via RTTI discovery).
				referentId = GetId(referent);
				if (!isSerialized(referentId)) {
					JsonObject fwd = new JsonObject();
					fwd.addProperty("id", referentId);
					fwd.addProperty("name", referent.getName());
					fwd.addProperty("unique_name", GetFwdId(referent));
					fwd.addProperty("size", 0);
					JsonArray opts = new JsonArray();
					opts.add("forwardref");
					fwd.add("options", opts);
					fwd.add("fields", new JsonArray());
					if (referent instanceof Enum) {
						fwd.addProperty("type", "LF_ENUM");
						fwd.addProperty("underlying_type", "0x0000");
					} else if (referent instanceof Union) {
						fwd.addProperty("type", "LF_UNION");
					} else {
						fwd.addProperty("type", "LF_STRUCTURE");
					}
					entries.add(fwd); // must precede the pointer entry in the type stream
					serialized.add(referentId);
					printf("[PDBGEN] fallback: emitting named forward decl for '%s' (referenced by pointer)\n",
							referent.getName());
				}
			} else {
				// Non-composite referent (e.g. function pointer chain, unknown primitive):
				// void* is the safest fallback and loses no useful name.
				printf("[PDBGEN] fallback: pointer referent '%s' unresolvable, using void*\n",
						GetIdUnmapped(referent));
				referentId = "0x0003"; // void
			}
		} else {
			referentId = GetId(x.getDataType());
		}
		JsonObject json = new JsonObject();
		json.addProperty("id", GetId(x));
		json.addProperty("type", "LF_POINTER");
		json.addProperty("referent_type", referentId);
		entries.add(json);
		return entries;
	}

	private JsonObject dump(Array x) {
		if (!isSerialized(x.getDataType()))
			return null;

		JsonObject json = new JsonObject();
		json.addProperty("id", GetId(x));
		json.addProperty("type", "LF_ARRAY");
		// TODO currently this is set to QWORD, is this different for x86/x64?
		json.addProperty("index_type", "0x0077");
		json.addProperty("element_type", GetId(x.getDataType()));
		json.addProperty("size", x.getLength());
		return json;
	}

	private JsonObject dump(Union x) {
		JsonArray members = new JsonArray();
		for (DataTypeComponent dt : x.getComponents()) {
			String typeId;
			if (!isSerialized(dt.getDataType())) {
				if (!useFallback) return null;
				int size = dt.getLength();
				String name = dt.getFieldName() != null ? dt.getFieldName() : dt.getDefaultFieldName();
				printf("[PDBGEN] fallback: union '%s' field '%s' type '%s' unresolvable, using %d-byte placeholder\n",
						x.getName(), name, GetIdUnmapped(dt.getDataType()), size);
				typeId = getPlaceholderTypeId(size);
			} else {
				typeId = GetId(dt.getDataType());
			}
			JsonObject json = new JsonObject();
			json.addProperty("type", "LF_MEMBER");
			json.addProperty("name", dt.getFieldName());
			json.addProperty("type_id", typeId);
			json.addProperty("offset", dt.getOffset());
			json.add("attributes", new JsonArray());
			members.add(json);
		}

		JsonObject json = new JsonObject();
		json.addProperty("id", GetFwdId(x));
		json.addProperty("type", "LF_UNION");
		json.addProperty("name", x.getName());
		json.addProperty("unique_name", GetFwdId(x));
		json.addProperty("size", x.getLength());
		json.add("fields", members);
		json.add("options", new JsonArray());
		return json;
	}

	private JsonObject dump(Enum x) {
		JsonArray fields = new JsonArray();
		for (long value : x.getValues()) {
			JsonObject json = new JsonObject();
			json.addProperty("name", x.getName(value));
			json.addProperty("value", value);
			fields.add(json);
		}
		JsonObject json = new JsonObject();
		json.addProperty("id", GetFwdId(x));
		json.addProperty("type", "LF_ENUM");
		json.addProperty("size", x.getLength());
		json.addProperty("underlying_type", "0x0074");
		json.addProperty("name", x.getName());
		json.addProperty("unique_name", GetFwdId(x));
		json.add("fields", fields);
		json.add("options", new JsonArray());
		return json;
	}

	private JsonObject dump(Structure x) {
		JsonArray fields = new JsonArray();
		for (DataTypeComponent dt : x.getComponents()) {
			String typeId;
			if (!isSerialized(dt.getDataType())) {
				if (!useFallback) return null;
				int size = dt.getLength();
				String name = dt.getFieldName() != null ? dt.getFieldName() : dt.getDefaultFieldName();
				printf("[PDBGEN] fallback: struct '%s' field '%s' type '%s' unresolvable, using %d-byte placeholder\n",
						x.getName(), name, GetIdUnmapped(dt.getDataType()), size);
				typeId = getPlaceholderTypeId(size);
			} else {
				typeId = GetId(dt.getDataType());
			}

			JsonObject json = new JsonObject();
			json.addProperty("type", "LF_MEMBER");
			json.addProperty("type_id", typeId);
			json.addProperty("offset", dt.getOffset());
			json.add("attributes", new JsonArray());
			if (dt.getFieldName() == null) {
				json.addProperty("name", dt.getDefaultFieldName());
			} else {
				json.addProperty("name", dt.getFieldName());
			}

			if (dt.isBitFieldComponent()) {
				// TODO implement this
				// BitFieldDataType bfdt = (BitFieldDataType) dt.getDataType();
			}

			fields.add(json);
		}

		JsonObject json = new JsonObject();
		json.addProperty("id", GetFwdId(x));
		json.addProperty("type", "LF_STRUCTURE");
		json.addProperty("name", x.getName());
		json.addProperty("size", x.getLength());
		json.addProperty("unique_name", GetFwdId(x));
		json.add("options", new JsonArray());
		json.add("fields", fields);
		return json;
	}

	private JsonObject dump(BitFieldDataType x) {
		if (!isSerialized(x.getBaseDataType()))
			return null;

		JsonObject json = new JsonObject();
		json.addProperty("id", GetId(x));
		json.addProperty("type", "LF_BITFIELD");
		json.addProperty("type_id", GetId(x.getBaseDataType()));
		json.addProperty("bit_offset", x.getBitOffset());
		json.addProperty("bit_size", x.getBitSize());
		return json;
	}

	private List<JsonObject> dump(FunctionDefinition x) {
		// // There should be a good way of determining class, but I haven't found it
		// yet
		// // So instead I'm just gonna check calling convention and lookup the type
		// manually.
		// if (x.getGenericCallingConvention() == GenericCallingConvention.thiscall) {
		// DataType clz = x.getArguments()[0].getDataType();
		// if (clz instanceof Pointer) {
		// clz = ((Pointer) clz).getDataType();
		// }
		// printf("%s::%s()\n", clz.getName(), x.getName());
		// }
		// printf("function [%s] %s %s\n", x.getName(), GetId(x),
		// x.getClass().getName());

		// we wait (return null) until we have dumped all the dependant types
		String returnTypeId;
		if (!isSerialized(x.getReturnType())) {
			if (!useFallback) return null;
			printf("[PDBGEN] fallback: function '%s' return type '%s' unresolvable, using void\n",
					x.getName(), GetIdUnmapped(x.getReturnType()));
			returnTypeId = "0x0003"; // void
		} else {
			returnTypeId = GetId(x.getReturnType());
		}
		JsonArray parameters = new JsonArray();
		for (ParameterDefinition p : x.getArguments()) {
			if (!isSerialized(p.getDataType())) {
				if (!useFallback) return null;
				printf("[PDBGEN] fallback: function '%s' param '%s' type '%s' unresolvable, using void*\n",
						x.getName(), p.getName(), GetIdUnmapped(p.getDataType()));
				parameters.add("0x0603"); // void* (64-bit pointer to void)
			} else {
				parameters.add(GetId(p.getDataType()));
			}
		}
		List<JsonObject> entries = new ArrayList<JsonObject>();

		JsonObject json = new JsonObject();
		json.addProperty("type", "LF_PROCEDURE");
		json.addProperty("id", GetId(x));
		json.addProperty("name", x.getName());
		json.addProperty("return_type", returnTypeId);
		json.addProperty("calling_convention", x.getCallingConventionName());
		json.add("options", new JsonArray());
		json.add("parameters", parameters);
		entries.add(json);

		json = new JsonObject();
		// We are creating a new id here just so it flows through our pipeline correctly
		// with the rest of the types.
		json.addProperty("type", "LF_FUNC_ID");
		json.addProperty("id", UUID.randomUUID().toString());
		json.addProperty("name", x.getName());
		json.addProperty("function_type", GetId(x));
		json.addProperty("parent_scope", "0x0000"); // placeholder
		entries.add(json);

		return entries;
	}

	private JsonObject dump(TypeDef dt) {
		DataType base = dt.getBaseDataType();
		if (!isSerialized(base)) {
			return null;
		}
		typedefs.put(GetIdUnmapped(dt), GetIdUnmapped(dt.getBaseDataType()));
		JsonObject json = new JsonObject();
		// json.addProperty("", null);
		return json;
	}

	private List<JsonObject> toJson(DataType dt) {
		if (dt instanceof FunctionDefinition) {
			return dump((FunctionDefinition) dt);
		}
		if (dt instanceof Pointer) {
			return dump((Pointer) dt);
		}

		List<JsonObject> entries = new ArrayList<JsonObject>();
		JsonObject json = null;
		if (dt instanceof BitFieldDataType) {
			json = dump((BitFieldDataType) dt);
		} else if (dt instanceof Array) {
			json = dump((Array) dt);
		} else if (dt instanceof Union) {
			json = dump((Union) dt);
		} else if (dt instanceof Enum) {
			json = dump((Enum) dt);
		} else if (dt instanceof Structure) {
			json = dump((Structure) dt);
		} else if (dt instanceof DefaultDataType) {
			// this is "undefined" which is predefined by codeview, so we will skip it here.
			return entries;
		} else if (dt instanceof TypeDef) {
			json = dump((TypeDef) dt);
			// Not required... we map typedefs to their underlying type before processing
			// the rest of the types
			// I have not found any CodeView type for typedefs, so we map the types (AFAIK
			// like the linker does).
			// implementing this *might* cleanup the output a little, but not sure if the
			// juice is worth the squeeze
			if (json == null) {
				return null;
			} else {
				return entries;
			}
		} else {
			if (dt != null)
				printf("[PDBGEN] Unknown Type: id=%s, name=%s, class=%s\n", GetId(dt), dt.getName(),
						dt.getClass().getName());
			else
				printf("[PDBGEN] Null Data Type: id=%s\n", GetId(dt));
		}

		if (json == null) {
			return null;
		}

		entries.add(json);
		return entries;
	}

	public void printMissing(DataType dt) {
		if (dt instanceof BuiltIn) {
			if (dt instanceof PointerDataType) {
				printMissing((Pointer) dt);
			} else {
				printf("[PDBGEN] missing: BuiltIn '%s' missing, size=%d\n", GetIdUnmapped(dt), dt.getLength());
			}
		} else if (dt instanceof FunctionDefinition) {
			printMissing((FunctionDefinition) dt);
		} else if (dt instanceof Pointer) {
			printMissing((Pointer) dt);
		} else if (dt instanceof Array) {
			printMissing((Array) dt);
		} else if (dt instanceof Structure) {
			printMissing((Structure) dt);
		} else if (dt instanceof Union) {
			printMissing((Union) dt);
		} else if (dt instanceof DefaultDataType) {
			printMissing((DefaultDataType) dt);
		} else if (dt instanceof TypeDef) {
			printMissing((TypeDef) dt);
		} else if (dt instanceof Enum) {
			printMissing((Enum) dt);
		} else if (dt instanceof BitFieldDataType) {
			printMissing((BitFieldDataType) dt);
		} else {
			if (dt != null)
				printf("[PDBGEN] missing: Unknown data type id='%s', type=%s\n", GetIdUnmapped(dt),
						dt.getClass().getName());
			else
				printf("[PDBGEN] missing: Null data type id='%s'\n", GetIdUnmapped(dt));
		}
	}

	public void printMissing(FunctionDefinition dt) {
		if (!isSerialized(dt.getReturnType())) {
			printf("[PDBGEN] missing: FunctionDefinition '%s' missing return type '%s'\n", GetIdUnmapped(dt),
					GetIdUnmapped(dt.getReturnType()));
		}

		for (ParameterDefinition argument : dt.getArguments()) {
			if (!isSerialized(argument.getDataType())) {
				printf("[PDBGEN] missing: FunctionDefinition '%s' missing argument type '%s' for '%s'\n",
						GetIdUnmapped(dt), GetIdUnmapped(argument.getDataType()), argument.getName());
			}
		}
	}

	public void printMissing(Pointer dt) {
		if (!isSerialized(dt.getDataType())) {
			printf("[PDBGEN] missing: Pointer '%s' missing base type '%s'\n", GetIdUnmapped(dt),
					GetIdUnmapped(dt.getDataType()));
		}
	}

	public void printMissing(Array dt) {
		if (!isSerialized(dt.getDataType())) {
			printf("[PDBGEN] missing: Array '%s' missing base type '%s'\n", GetIdUnmapped(dt),
					GetIdUnmapped(dt.getDataType()));
		}
	}

	public void printMissing(Structure dt) {
		for (DataTypeComponent component : dt.getComponents()) {
			if (!isSerialized(component.getDataType())) {
				printf("[PDBGEN] missing: Structure '%s' missing component type '%s' for field '%s'\n",
						GetIdUnmapped(dt), GetIdUnmapped(component.getDataType()), component.getFieldName());
			}
		}
	}

	public void printMissing(Union dt) {
		for (DataTypeComponent component : dt.getComponents()) {
			if (!isSerialized(component.getDataType())) {
				printf("[PDBGEN] missing: Union '%s' missing component type '%s'\n", GetIdUnmapped(dt),
						GetIdUnmapped(component.getDataType()));
			}
		}
	}

	public void printMissing(Enum dt) {
		printf("[PDBGEN] missing: Enum missing '%s'\n", GetIdUnmapped(dt));
	}

	public void printMissing(DefaultDataType dt) {
		printf("[PDBGEN] missing: DefaultDataType missing '%s'\n", GetIdUnmapped(dt));
	}

	public void printMissing(TypeDef dt) {
		if (!isSerialized(dt.getBaseDataType())) {
			printf("[PDBGEN] missing: TypeDef '%s' missing base type '%s'\n", GetIdUnmapped(dt),
					GetIdUnmapped(dt.getBaseDataType()));
		}
	}

	public void printMissing(BitFieldDataType dt) {
		if (!isSerialized(dt.getBaseDataType())) {
			printf("[PDBGEN] missing: BitField '%s' missing base type '%s'\n", GetIdUnmapped(dt),
					GetIdUnmapped(dt.getBaseDataType()));
		}
	}

	public JsonArray toJson(List<DataType> datatypes) throws CancelledException {
		monitor.setMessage("Extracting DataTypes");
		monitor.initialize(datatypes.size());
		monitor.setIndeterminate(false);
		monitor.setShowProgressValue(true);
		monitor.setCancelEnabled(true);
		// sort so less complex data types are processed first
		datatypes.sort((a, b) -> Integer.compare(getSize(a), getSize(b)));

		// Build forward declarations for everything, basically because I'm lazy.
		// We should only need to add forward declarations for data types that have
		// cyclic dependencies.
		JsonArray json = buildForwardDeclarations(datatypes);

		// A naive ordered serialization. We continually iterate through the list,
		// serializing data types only once they have had all their dependencies
		// serialized.
		// we stop looping over the list once we fail to serialize at least one data
		// type.
		// Any data types that are missing dependent types will be left in the input
		// list.
		long total = datatypes.size();
		monitor.initialize(total);
		while (!datatypes.isEmpty()) {
			boolean changed = false;
			Iterator<DataType> itr = datatypes.iterator();
			while (itr.hasNext()) {
				updateMonitor("Converting datatypes to json");
				DataType dt = itr.next();
				List<JsonObject> entries = toJson(dt);
				if (entries == null) {
					monitor.setMaximum(monitor.getMaximum() + 1); // increase counter since we need to come back
					continue; // waiting for dependencies to added first
				}

				if (debug) printf("[PDBGEN] dumped: id=%s, original=%s\n", GetId(dt), GetIdUnmapped(dt));
				itr.remove();
				for (JsonObject entry : entries) {
					json.add(entry);
				}
				setSerialized(dt);
				changed = true;
				monitor.incrementProgress(1);
			}

			if (!changed) {
				break; // we failed to remove any data types.
			}
		}
		long deferred = monitor.getMaximum() - total;
		printf("[PDBGEN] datatype deferred serialization %d/%d (%,.2f%%)\n", deferred, total,
				(float) deferred / total * 100);

		// Phase 2: types still in the list have truly unresolvable deps (e.g. -BAD-
		// fields, filtered-out types). Pre-emit sized placeholder LF_ARRAY records,
		// then retry with useFallback=true so each dump() substitutes instead of
		// returning null.
		if (!datatypes.isEmpty()) {
			printf("[PDBGEN] fallback: %d types unresolvable after Phase 1, starting fallback pass\n",
					datatypes.size());
			emitPlaceholderArrayTypes(datatypes, json);

			useFallback = true;
			boolean madeProgress = true;
			while (madeProgress && !datatypes.isEmpty()) {
				madeProgress = false;
				Iterator<DataType> itr2 = datatypes.iterator();
				while (itr2.hasNext()) {
					updateMonitor("Fallback serialization");
					DataType dt = itr2.next();
					List<JsonObject> entries = toJson(dt);
					if (entries == null) continue;
					if (debug) printf("[PDBGEN] fallback dumped: %s\n", GetId(dt));
					itr2.remove();
					for (JsonObject entry : entries) json.add(entry);
					setSerialized(dt);
					madeProgress = true;
				}
			}
			useFallback = false;
		}

		// Log anything that even fallback couldn't handle
		monitor.initialize(datatypes.size());
		for (DataType dt : datatypes) {
			updateMonitor("Checking for missing datatypes");
			printMissing(dt);
		}

		printf("[PDBGEN] missing after fallback: %d\n", datatypes.size());
		return json;
	}

	public JsonArray buildForwardDeclarations(List<DataType> datatypes) {
		// some data that is common to all forward declarations
		JsonArray fields = new JsonArray();
		JsonArray options = new JsonArray();
		options.add("forwardref");

		JsonArray objs = new JsonArray();
		for (DataType dt : datatypes) {
			JsonObject json = new JsonObject();

			// the forward declared type and the actual type need different IDs
			// to make things easy, we use the original id in the forward declaration
			// so we do not need to rewrite the all the references.
			// We create a new Id for the actual type, because nothing else references it.
			json.addProperty("id", GetId(dt));

			if (dt instanceof Enum) {
				json.addProperty("type", "LF_ENUM");
				json.addProperty("underlying_type", "0x0000");
			} else if (dt instanceof Union) {
				json.addProperty("type", "LF_UNION");
			} else if (dt instanceof Structure) {
				json.addProperty("type", "LF_STRUCTURE");
			} else {
				continue; // we do not need to forward declare this type
			}

			// PDB resolves forward declarations by looking for other types with the same
			// unique name,
			// if it does not find one, it will match on name instead.
			// I'm not sure if this can cause inconsistency if unique_name is not used...
			// To avoid issues, we use a uuid for the unique name to consistently match
			// correctly.
			json.addProperty("name", dt.getName());
			json.addProperty("unique_name", GetFwdId(dt));
			json.addProperty("size", 0);
			json.add("options", options);
			json.add("fields", fields);

			objs.add(json);
			setSerialized(dt);
		}
		return objs;
	}

	// Returns the CodeView type id to use as a sized placeholder in fallback mode.
	// For sizes matching a primitive (1/2/4/8/16) we reuse that primitive directly.
	// For other sizes an LF_ARRAY record must have been pre-emitted via
	// emitPlaceholderArrayTypes() before this is called.
	private String getPlaceholderTypeId(int size) {
		switch (size) {
			case 1:  return "0x0069"; // T_UINT1  (byte)
			case 2:  return "0x0021"; // T_UINT2  (ushort)
			case 4:  return "0x0075"; // T_UINT4  (uint)
			case 8:  return "0x0077"; // T_UINT8  (ulonglong)
			case 16: return "0x0079"; // T_UINT16 (uint128)
			default:
				// non-standard size: look up the pre-emitted LF_ARRAY placeholder
				return placeholderTypeIds.getOrDefault(size, "0x0077"); // last-resort: ulonglong
		}
	}

	// Scans remaining composites for components whose types are still unresolvable,
	// collects the unique non-primitive sizes, and emits an LF_ARRAY-of-byte record
	// for each into `into`. Must be called before the Phase 2 fallback loop so the
	// array types appear earlier in the type stream than the structs that use them.
	private void emitPlaceholderArrayTypes(List<DataType> remaining, JsonArray into) {
		Set<Integer> primitives = new HashSet<>();
		primitives.add(1); primitives.add(2); primitives.add(4); primitives.add(8); primitives.add(16);

		Set<Integer> neededSizes = new HashSet<>();
		for (DataType dt : remaining) {
			DataTypeComponent[] components = null;
			if (dt instanceof Structure)
				components = ((Structure) dt).getComponents();
			else if (dt instanceof Union)
				components = ((Union) dt).getComponents();
			if (components == null) continue;
			for (DataTypeComponent c : components) {
				if (!isSerialized(c.getDataType()) && !primitives.contains(c.getLength()))
					neededSizes.add(c.getLength());
			}
		}

		for (int size : neededSizes) {
			if (placeholderTypeIds.containsKey(size)) continue;
			String id = "__placeholder_array_" + size;
			placeholderTypeIds.put(size, id);
			serialized.add(id); // mark so struct members can reference it immediately
			JsonObject arr = new JsonObject();
			arr.addProperty("id", id);
			arr.addProperty("type", "LF_ARRAY");
			arr.addProperty("index_type", "0x0077");
			arr.addProperty("element_type", "0x0069"); // byte
			arr.addProperty("size", size);
			into.add(arr);
			printf("[PDBGEN] placeholder: emitting %d-byte array type '%s'\n", size, id);
		}
	}

	private void collectReachable(DataType dt, Set<DataType> reachable) {
		if (dt == null || reachable.contains(dt))
			return;
		reachable.add(dt);
		if (dt instanceof FunctionDefinition) {
			FunctionDefinition fd = (FunctionDefinition) dt;
			collectReachable(fd.getReturnType(), reachable);
			for (ParameterDefinition p : fd.getArguments())
				collectReachable(p.getDataType(), reachable);
		} else if (dt instanceof Structure) {
			for (DataTypeComponent c : ((Structure) dt).getComponents())
				collectReachable(c.getDataType(), reachable);
		} else if (dt instanceof Union) {
			for (DataTypeComponent c : ((Union) dt).getComponents())
				collectReachable(c.getDataType(), reachable);
		} else if (dt instanceof Array) {
			collectReachable(((Array) dt).getDataType(), reachable);
		} else if (dt instanceof Pointer) {
			collectReachable(((Pointer) dt).getDataType(), reachable);
		} else if (dt instanceof TypeDef) {
			collectReachable(((TypeDef) dt).getBaseDataType(), reachable);
		} else if (dt instanceof BitFieldDataType) {
			collectReachable(((BitFieldDataType) dt).getBaseDataType(), reachable);
		}
	}

	public List<DataType> getAllDataTypes() throws Exception {
		List<DataType> datatypes = new ArrayList<DataType>();
		// this function, despite its name, does not return all datatypes :(
		// we are going to have to go find the missing ones.
		currentProgram.getDataTypeManager().getAllDataTypes(datatypes);
		int total = datatypes.size();
		// for some reason, Ghidra does not include BitField DataTypes in
		// getAllDataTypes, so we manually add them here.
		Iterator<Composite> composites = currentProgram.getDataTypeManager().getAllComposites();
		while (composites.hasNext()) {
			updateMonitor("Getting composites");
			Composite composite = composites.next();
			for (DataTypeComponent component : composite.getComponents()) {
				datatypes.add(component.getDataType());
			}
		}

		// functions are not apart of the data type manager apparently.
		Iterator<Function> functions = currentProgram.getFunctionManager().getFunctionsNoStubs(true);
		total = currentProgram.getFunctionManager().getFunctionCount();
		monitor.initialize(total);
		item = 0;
		while (functions.hasNext()) {
			updateMonitor("Getting functions");
			Function function = functions.next();
			if (function.isThunk())
				continue;
			if (function.isExternal())
				continue;
			FunctionSignature signature = function.getSignature();
			if (signature instanceof FunctionDefinition) {
				datatypes.add((FunctionDefinition) signature);
				entrypoints.put(function.getEntryPoint(), (FunctionDefinition) signature);
				for (ParameterDefinition argument : signature.getArguments()) {
					datatypes.add(argument.getDataType());
				}
			}
		}

		// remove data types that we do not need to serialize for the pdb
		Iterator<DataType> itr = datatypes.iterator();
		item = 0;
		while (itr.hasNext()) {
			updateMonitor("Checking datatypes");
			DataType dt = itr.next();
			if (dt instanceof PointerDataType) {
				// technically a BuiltInDataType, however some thiscall "this" parameters are
				// defined like this :(
				continue;
			} else if (dt instanceof BuiltIn) {
				if (typedefs.containsKey(dt.getName())) {
					String value = typedefs.get(dt.getName());
					typedefs.put(GetIdUnmapped(dt), value);
				}
				itr.remove();
				if (isSerialized(dt)) {
					// normal built in (int, bool, char*, etc)
					continue;
				}
				// printf("[PDBGEN] removed: %s (%s)\n", dt.getName(), dt.getClass().getName());
			} else if (dt instanceof TypeDef) {
				// any other typedefs that are not explictly defined by codeview
				// DataType basetype = ((TypeDef) dt).getBaseDataType();
				// typedefs.put(GetIdUnmapped(dt), GetIdUnmapped(basetype));
				// typedefs.put(dt.getName(), GetIdUnmapped(basetype));
				// itr.remove();
			}
		}

		if (filterToFunctionTypes) {
			int before = datatypes.size();
			Set<DataType> reachable = new HashSet<>();
			for (FunctionDefinition fd : entrypoints.values())
				collectReachable(fd, reachable);
			datatypes.removeIf(dt -> !(dt instanceof FunctionDefinition) && !reachable.contains(dt));
			printf("[PDBGEN] reachability filter: %d -> %d types (%d functions)\n",
					before, datatypes.size(), entrypoints.size());
		}

		return datatypes;
	}

	public List<Symbol> getAllSymbols() throws Exception {
		List<Symbol> symbols = new ArrayList<Symbol>();
		monitor.initialize(currentProgram.getSymbolTable().getNumSymbols());
		item = 0;
		for (Symbol symbol : currentProgram.getSymbolTable().getAllSymbols(false)) {
			updateMonitor("Getting Symbols ");
			if (symbol.isExternal())
				continue;
			symbols.add(symbol);
		}
		return symbols;
	}

	public JsonArray toJsonSymbols(List<Symbol> symbols) throws CancelledException {
		monitor.initialize(symbols.size());
		monitor.setShowProgressValue(true);
		monitor.setIndeterminate(false);
		monitor.setCancelEnabled(true);

		JsonArray objs = new JsonArray();
		FunctionManager manager = currentProgram.getFunctionManager();
		monitor.initialize(symbols.size());
		item = 0;
		for (Symbol symbol : symbols) {
			updateMonitor("Extracting Symbols");
			SymbolType stype = symbol.getSymbolType();
			// SourceType source = symbol.getSource();
			Address address = symbol.getAddress();

			// // We can do some interesting filtering based on where the symbol came from.
			// if (source == SourceType.ANALYSIS) {
			// } else if (source == SourceType.DEFAULT) {
			// } else if (source == SourceType.IMPORTED) {
			// } else if (source == SourceType.USER_DEFINED) {
			// }

			String name = symbol.getName(true);
			if (stype == SymbolType.CLASS) {
			} else if (stype == SymbolType.FUNCTION) {
				Function function = manager.getFunctionAt(address);
				// we rename any thunks to easily distinguish them from the actual functions
				if (function.isThunk() && !name.startsWith("thunk_")) {
					name = "thunk_" + name;
				}

				// A function whose entry is not in an executable section cannot be a
				// CodeView procedure (S_GPROC32 needs a code segment); pdbgen aborts the
				// entire PDB on the unmappable address. Emit it as a public data symbol so
				// the name survives and generation continues. Seen for analysis false
				// positives in .data/.rdata and CommonLib inline accessors whose
				// RELOCATION_ID points at the singleton/array data they return.
				ghidra.program.model.mem.MemoryBlock block = currentProgram.getMemory().getBlock(address);
				if (block == null || !block.isExecute()) {
					JsonObject data = new JsonObject();
					data.addProperty("type", "S_PUB32");
					data.addProperty("name", name);
					data.addProperty("address", address.getUnsignedOffset());
					data.addProperty("function", false);
					objs.add(data);
					continue;
				}

				JsonObject json = new JsonObject();
				json.addProperty("type", "S_PUB32");
				json.addProperty("name", name);
				json.addProperty("address", address.getUnsignedOffset());
				json.addProperty("function", true);
				objs.add(json);

				if (function.isThunk())
					continue;

				// for what ever reason, the ID of the FunctionSignature is different from when
				// we dumps the types,
				// so we cache the original type, and use the function's address to find it now.
				FunctionDefinition definition = entrypoints.get(address);

				String id = GetId(definition);
				// printf("signature [%s] %s %s", definition.getName(), id,
				// definition.getClass().getName());

				// // I dont have a good way of looking up the FunctionDefinition id from here.
				// will probably need a refactor.
				Address start = function.getBody().getMinAddress();
				Address end = function.getBody().getMaxAddress();

				if (!start.hasSameAddressSpace(end)) {
					// TODO: Generate symbols in a sane way when there are multiple "address ranges"
					// for a function.
					// The above functions will return the start of the lowest range, and the end of
					// the highest range
					// which is absolutely not what we want, so we are gonna skip them for now.
					continue;
				}

				// S_GPROC32
				json = new JsonObject();
				json.addProperty("type", "S_GPROC32");
				json.addProperty("name", name);
				json.addProperty("address", start.getUnsignedOffset());
				json.addProperty("code_size", end.subtract(start) + 1);
				json.addProperty("end", 0);
				json.addProperty("function_type", id);
				json.addProperty("debug_start", 0);
				json.addProperty("debug_end", 0);
				json.addProperty("parent", "0x0000");
				json.add("flags", new JsonArray());
				objs.add(json);

				json = new JsonObject();
				json.addProperty("type", "S_END");
				objs.add(json);

				// // S_PROCREF
				// fmt = "{\"type\": \"S_PROCREF\", \"name\": \"%s\", \"address\": %d,
				// \"code_size\": \"%d\", \"function_type\": \"%s\", \"debug_start\": %d,
				// \"debug_end\": %d, \"parent\": \"%s\", \"flags\": []}";
				// lines.add(String.format(fmt, name, start.getUnsignedOffset(),
				// end.subtract(start)+1, id, 0, 0, "0x0000"));
			} else if (stype == SymbolType.GLOBAL || stype == SymbolType.GLOBAL_VAR) {
				JsonObject json = new JsonObject();
				json.addProperty("type", "S_PUB32");
				json.addProperty("name", name);
				json.addProperty("address", address.getUnsignedOffset());
				json.addProperty("function", false);
				objs.add(json);

			} else if (stype == SymbolType.LABEL) {
			} else if (stype == SymbolType.CLASS) {
			} else if (stype == SymbolType.LIBRARY) {
			} else if (stype == SymbolType.LOCAL_VAR) {
			} else if (stype == SymbolType.NAMESPACE) {
			} else if (stype == SymbolType.PARAMETER) {
			} else {
				// unknown symbol type
			}
		}
		return objs;
	}

	public void initializeTypeDefs() {
		// map Ghidra built-in types that are predefined by CodeView
		// these do not have a UniversalID so we reference them by their name instead.
		// note: name may not be unique, but its all i have found so far.

		Map<String, String> aliases = new HashMap<String, String>();
		aliases.put("/undefined", "0x0003"); // we have to do this manually in GetIdUnmapped
		aliases.put("BuiltInTypes:/null", "0x0000");
		aliases.put("BuiltInTypes:/void", "0x0003");
		aliases.put("BuiltInTypes:/bool", "0x0030");
		aliases.put("BuiltInTypes:/byte", "0x0069");
		aliases.put("BuiltInTypes:/sbyte", "0x0068");
		aliases.put("BuiltInTypes:/char", "0x0070");
		aliases.put("BuiltInTypes:/wchar_t", "0x0071");
		aliases.put("BuiltInTypes:/char16_t", "0x007A");
		aliases.put("BuiltInTypes:/char32_t", "0x007B");
		aliases.put("BuiltInTypes:/uchar", "0x0020");
		aliases.put("BuiltInTypes:/wchar16", "0x007A");
		aliases.put("BuiltInTypes:/wchar32", "0x007B");
		aliases.put("BuiltInTypes:/short", "0x0011");
		aliases.put("BuiltInTypes:/ushort", "0x0021");
		aliases.put("BuiltInTypes:/int", "0x0074");
		aliases.put("BuiltInTypes:/uint", "0x0075");
		aliases.put("BuiltInTypes:/long", "0x0012");
		aliases.put("BuiltInTypes:/ulong", "0x0022");
		aliases.put("BuiltInTypes:/longlong", "0x0076");
		aliases.put("BuiltInTypes:/ulonglong", "0x0077");
		aliases.put("BuiltInTypes:/uint128_t", "0x0079");
		aliases.put("BuiltInTypes:/word", "0x0073");
		aliases.put("BuiltInTypes:/dword", "0x0075");
		aliases.put("BuiltInTypes:/qword", "0x0077");
		aliases.put("BuiltInTypes:/float", "0x0040");
		aliases.put("BuiltInTypes:/double", "0x0041");
		aliases.put("BuiltInTypes:/float10", "0x0042");

		aliases.put("BuiltInTypes:/string", "0x0670");
		aliases.put("BuiltInTypes:/string-utf8", "0x0670");
		aliases.put("BuiltInTypes:/unicode", "0x067A");
		aliases.put("BuiltInTypes:/unicode32", "0x067B");
		aliases.put("BuiltInTypes:/TerminatedCString", "0x0670");
		aliases.put("BuiltInTypes:/ImageBaseOffset32", "0x0075");
		aliases.put("BuiltInTypes:/ImageBaseOffset64", "0x0076");

		aliases.put("BuiltInTypes:/uint3", "0x0075");
		aliases.put("BuiltInTypes:/longdouble", "0x0042");

		aliases.put("BuiltInTypes:/undefined1", "0x0069");
		aliases.put("BuiltInTypes:/undefined2", "0x0021");
		aliases.put("BuiltInTypes:/undefined3", "0x0022");
		aliases.put("BuiltInTypes:/undefined4", "0x0022");
		aliases.put("BuiltInTypes:/undefined5", "0x0077");
		aliases.put("BuiltInTypes:/undefined6", "0x0077");
		aliases.put("BuiltInTypes:/undefined7", "0x0077");
		aliases.put("BuiltInTypes:/undefined8", "0x0077");

		aliases.put("BuiltInTypes:/GUID", "0x0079");
		aliases.put("BuiltInTypes:/IMAGE_RICH_HEADER", "0x0069");
		aliases.put("BuiltInTypes:/PEx64_UnwindInfo", "0x069");

		for (String key : aliases.keySet()) {
			String value = aliases.get(key);
			printf("alias: %s -> %s\n", key, value);
			DataType dt = currentProgram.getDataTypeManager().getDataType(key);
			String typeid = GetIdUnmapped(dt);

			typedefs.put(key, value);
			typedefs.put(typeid, value);

			serialized.add(key);
			serialized.add(typeid);
		}

		for (String value : aliases.values()) {
			if (value.startsWith("0x")) {
				serialized.add(value);
			}
		}
	}

	public static List<String> readAll(InputStream in) throws IOException {
		BufferedReader reader = new BufferedReader(new InputStreamReader(in));
		List<String> lines = new ArrayList<String>();
		while (reader.ready()) {
			lines.add(reader.readLine());
		}
		return lines;
	}

	// Drains all remaining lines from a stream that is known to be at EOF (i.e.
	// after the process has exited). Unlike readAll(), this blocks until the
	// stream closes rather than relying on ready(), so no output is lost.
	public static List<String> readAllBlocking(InputStream in) throws IOException {
		BufferedReader reader = new BufferedReader(new InputStreamReader(in));
		List<String> lines = new ArrayList<String>();
		String line;
		while ((line = reader.readLine()) != null) {
			lines.add(line);
		}
		return lines;
	}

	public void run() throws Exception {
		if (state.getTool() != null) {
			ConsoleService console = state.getTool().getService(ConsoleService.class);
			console.clearMessages();
		}

		// clear types from the last run
		typedefs.clear();
		serialized.clear();
		forwardDeclared.clear();
		placeholderTypeIds.clear();
		useFallback = false;
		sectionTimer.clear();
		sectionItems.clear();
		sectionItemCount = 0;
		lastStatus = "";
		start = Instant.now();

		// setup typedefs so we can map to basic types
		initializeTypeDefs();

		JsonObject json = new JsonObject();
		// Now serialize all the data types (in dependency order)
		json.add("types", toJson(getAllDataTypes()));
		json.add("symbols", toJsonSymbols(getAllSymbols()));

		// Ghidra has unhelpfully set the path to \C:\\Something\ this gives as a normal
		// c:\\Something
		String recordedExePath = Path.fromPathString(currentProgram.getExecutablePath()).toString();
		printf("executable: %s\n", recordedExePath);
		String output = FilenameUtils.removeExtension(recordedExePath).concat(".pdb");
		String jsonpath = FilenameUtils.removeExtension(recordedExePath).concat(".json");
		String exepath = resolveExecutablePath(recordedExePath);

		updateMonitor("Saving files");
		boolean skipPdbGen = false;
		try (FileWriter w = new FileWriter(jsonpath)) {
			if (prettyPrint) {
				Gson gson = new GsonBuilder().setPrettyPrinting().create();
				JsonElement je = JsonParser.parseString(json.toString());
				String prettyJsonString = gson.toJson(je);
				w.write(prettyJsonString);
			} else {
				w.write(json.toString());
			}
		} catch (FileNotFoundException e) {
			skipPdbGen = true;
			printf("Unable to save: %s\n;", e);
		}

		if (exepath == null) {
			skipPdbGen = true;
			printf("[PDBGEN] FAILED: executable not found at '%s' and no file in that folder matches this program's MD5 -- skipping pdbgen.exe. JSON was still written to %s\n",
					recordedExePath, jsonpath);
		}
		// simple configurable path
		// Ghidra will cache the default value here, and it will prefer its internal
		// cached version over our default path :(.
		// output = askString("location to save", "select a location to save the output
		// pdb", output);

		if (!skipPdbGen) {
			monitor.setIndeterminate(true);
			monitor.setCancelEnabled(true);
			ProcessBuilder pdbgen = new ProcessBuilder();
			// Pass the saved JSON file directly — avoids re-serializing and piping
			// the full JSON through stdin.
			pdbgen.command("pdbgen.exe", exepath, jsonpath, "--output", output);

			Process proc = pdbgen.start();
			while (proc.isAlive()) {
				updateMonitor("Running pdbgen.exe");
				if (monitor.isCancelled()) {
					updateMonitor("Stopping pdbgen.exe");
					proc.destroy();
				}
				for (String line : readAll(proc.getInputStream())) {
					println(line);
				}

				for (String line : readAll(proc.getErrorStream())) {
					printerr(line);
				}
				proc.waitFor(100, TimeUnit.MILLISECONDS);
			}
			// Drain any output written after the last poll but before process exit.
			for (String line : readAllBlocking(proc.getInputStream())) {
				println(line);
			}
			for (String line : readAllBlocking(proc.getErrorStream())) {
				printerr(line);
			}
			int exitCode = proc.exitValue();
			if (exitCode != 0) {
				printf("[PDBGEN] pdbgen.exe exited with code %d\n", exitCode);
			}
		}
		printSectionTimers();
		printPdbSummary(output, json);
		return;
	}
}
