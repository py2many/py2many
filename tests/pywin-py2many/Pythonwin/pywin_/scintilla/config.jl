module config
using Printf
using PyCall
win32api = pyimport("win32api")
import win32traceutil

import string
include("keycodes.jl")
import marshal
import stat

import win32com_.gen_py
import glob
import importlib.util

abstract type AbstractConfigManager end
debugging = 0
if debugging != 0
    function trace()
        write(sys.stderr, join(map(str, args), " ") + "\n")
    end

else
    trace = () -> nothing
end
compiled_config_version = 3
function split_line(line, lineno)::Tuple
    comment_pos = find(line, "#")
    if comment_pos >= 0
        line = line[begin:comment_pos]
    end
    sep_pos = rfind(line, "=")
    if sep_pos == -1
        if strip(line)
            @printf("Warning: Line %d: %s is an invalid entry", (lineno, repr(line)))
            return (nothing, nothing)
        end
        return ("", "")
    end
    return (strip(line[begin:sep_pos]), strip(line[sep_pos+2:end]))
end

function get_section_header(line)::Tuple
    if line[1] == "["
        end_ = find(line, "]")
        if end_ == -1
            end_ = length(line)
        end
        rc = lower(line[2:end_])
        try
            i = index(rc, ":")
            return (rc[begin:i], rc[i+2:end])
        catch exn
            if exn isa ValueError
                return (rc, "")
            end
        end
    end
    return (nothing, nothing)
end

function find_config_file(f)
    return join
end

function find_config_files()
    return [
        split(os.path, x)[2] for x in [splitext(os.path, x)[1] for x in glob(glob, join)]
    ]
end

mutable struct ConfigManager <: AbstractConfigManager
    filename::String
    last_error
    key_to_events::Dict
    basename
    cache

    ConfigManager(f) = begin
        if hasattr(f, "readline")
            fp = f
            filename = "<config string>"
            compiled_name = nothing
        else
            try
                f = find_config_file(f)
                src_stat = os.stat(f)
            catch exn
                if exn isa os.error
                    report_error("Config file \'%s\' not found" % f)
                    return
                end
            end
            filename = f
            basename = os.path.basename(f)
            trace("Loading configuration", basename)
            compiled_name = os.path.splitext(f)[0] + ".cfc"
            try
                cf = readline(compiled_name)
                try
                    ver = marshal.load(cf)
                    ok = compiled_config_version == ver
                    if ok
                        kblayoutname = marshal.load(cf)
                        magic = marshal.load(cf)
                        size = marshal.load(cf)
                        mtime = marshal.load(cf)
                        if magic == importlib.util.MAGIC_NUMBER &&
                           win32api.GetKeyboardLayoutName() == kblayoutname &&
                           src_stat[stat.ST_MTIME] == mtime &&
                           src_stat[stat.ST_SIZE] == size
                            cache = marshal.load(cf)
                            trace("Configuration loaded cached", compiled_name)
                            return
                        end
                    end
                finally
                    cf.close()
                end
            catch exn
                if exn isa (os.error, IOError, EOFError)
                    #= pass =#
                end
            end
            fp = readline(f)
        end
        while line
            section, subsection = get_section_header(line)
            while line && section === nothing
                line = fp.readline()
                if !(line)
                    break
                end
                lineno = lineno + 1
                section, subsection = get_section_header(line)
            end
            if !(line)
                break
            end
            if section == "keys"
                line, lineno = _load_keys(subsection, fp, lineno)
            elseif section == "extensions"
                line, lineno = _load_extensions(subsection, fp, lineno)
            elseif section == "idle extensions"
                line, lineno = _load_idle_extensions(subsection, fp, lineno)
            elseif section == "general"
                line, lineno = _load_general(subsection, fp, lineno)
            else
                report_error("Unrecognised section header \'%s:%s\'" % (section, subsection))
                line = fp.readline()
                lineno = lineno + 1
            end
        end
        if !cache.get("keys")
            report_error("No keyboard definitions were loaded")
        end
        if !(last_error) && compiled_name
            try
                cf = readline(compiled_name)
                marshal.dump(compiled_config_version, cf)
                marshal.dump(win32api.GetKeyboardLayoutName(), cf)
                marshal.dump(importlib.util.MAGIC_NUMBER, cf)
                marshal.dump(src_stat[stat.ST_SIZE], cf)
                marshal.dump(src_stat[stat.ST_MTIME], cf)
                marshal.dump(cache, cf)
                cf.close()
            catch exn
                if exn isa (IOError, EOFError)
                    #= pass =#
                end
            end
        end
        new(f)
    end
end
function configure(self::ConfigManager, editor, subsections = nothing)
    if subsections === nothing
        subsections = []
    end
    subsections = [""] + subsections
    general = get_data(self, "general")
    if general
        parents = get(general, "based on", [])
        for parent in parents
            trace("Configuration based on", parent, "- loading.")
            parent = __class__(self, parent)
            configure(parent, editor, subsections)
            if parent.last_error
                report_error(self, parent.last_error)
            end
        end
    end
    bindings = editor.bindings
    codeob = get_data(self, "extension code")
    if codeob != nothing
        ns = Dict()
        try
            exec(codeob, ns)
        catch exn
            current_exceptions() != [] ? current_exceptions()[end] : nothing
            report_error(self, "Executing extension code failed")
            ns = nothing
        end
        if ns
            num = 0
            for (name, func) in collect(items(ns))
                if type_(func) == types.FunctionType && name[begin:1] != "_"
                    bind(bindings, name, func)
                    num = num + 1
                end
            end
            trace("Configuration Extension code loaded", num, "events")
        end
    end
    for subsection in subsections
        for ext in get(get_data(self, "idle extensions", Dict()), subsection, [])
            try
                IDLEExtension(editor.idle, ext)
                trace("Loaded IDLE extension", ext)
            catch exn
                report_error(self, "Can not load the IDLE extension \'%s\'" % ext)
            end
        end
    end
    subsection_keymap = get_data(self, "keys")
    num_bound = 0
    for subsection in subsections
        keymap = get(subsection_keymap, subsection, Dict())
        update_keymap(bindings, keymap)
        num_bound = num_bound + length(keymap)
    end
    trace("Configuration bound", num_bound, "keys")
end

function get_key_binding(self::ConfigManager, event, subsections = nothing)
    if subsections === nothing
        subsections = []
    end
    subsections = [""] + subsections
    subsection_keymap = get_data(self, "keys")
    for subsection in subsections
        map = get(self.key_to_events, subsection)
        if map === nothing
            map = Dict()
            keymap = get(subsection_keymap, subsection, Dict())
            for (key_info, map_event) in collect(items(keymap))
                map[map_event] = key_info
            end
            self.key_to_events[subsection] = map
        end
        info = get(map, event)
        if info != nothing
            return make_key_name(keycodes, info[1], info[2])
        end
    end
    return nothing
end

function report_error(self::ConfigManager, msg)
    self.last_error = msg
    @printf("Error in %s: %s", (self.filename, msg))
end

function report_warning(self::ConfigManager, msg)
    @printf("Warning in %s: %s", (self.filename, msg))
end

function _readline(self::ConfigManager, fp, lineno, bStripComments = 1)::Tuple
    line = readline(fp)
    lineno = lineno + 1
    if line
        bBreak = get_section_header(line)[1] != nothing
        if bStripComments && !(bBreak)
            pos = find(line, "#")
            if pos >= 0
                line = line[begin:pos] * "\n"
            end
        end
    else
        bBreak = 1
    end
    return (line, lineno, bBreak)
end

function get_data(self::ConfigManager, name, default = nothing)
    return get(self.cache, name, default)
end

function _save_data(self::ConfigManager, name, data)
    self.cache[name+1] = data
    return data
end

function _load_general(self::ConfigManager, sub_section, fp, lineno)::Tuple
    map = Dict()
    while true
        line, lineno, bBreak = _readline(self, fp, lineno)
        if bBreak
            break
        end
        key, val = split_line(line, lineno)
        if !(key)
            continue
        end
        key = lower(key)
        l = get(map, key, [])
        append(l, val)
        map[key] = l
    end
    _save_data(self, "general", map)
    return (line, lineno)
end

function _load_keys(self::ConfigManager, sub_section, fp, lineno)::Tuple
    main_map = get_data(self, "keys", Dict())
    map = get(main_map, sub_section, Dict())
    while true
        line, lineno, bBreak = _readline(self, fp, lineno)
        if bBreak
            break
        end
        key, event = split_line(line, lineno)
        if !(event)
            continue
        end
        sc, flag = parse_key_name(keycodes, key)
        if sc === nothing
            report_warning(self, "Line %d: Invalid key name \'%s\'" % (lineno, key))
        else
            map[(sc, flag)+1] = event
        end
    end
    main_map[sub_section+1] = map
    _save_data(self, "keys", main_map)
    return (line, lineno)
end

function _load_extensions(self::ConfigManager, sub_section, fp, lineno)::Tuple
    start_lineno = lineno
    lines = []
    while true
        line, lineno, bBreak = _readline(self, fp, lineno, 0)
        if bBreak
            break
        end
        push!(lines, line)
    end
    try
        c = compile("\n" * start_lineno + join(lines, ""), self.filename, "exec")
        _save_data(self, "extension code", c)
    catch exn
        let details = exn
            if details isa SyntaxError
                errlineno = details.lineno + start_lineno
                report_error(
                    self,
                    "Compiling extension code failed:\r\nFile: %s\r\nLine %d\r\n%s" %
                    (details.filename, errlineno, details.msg),
                )
            end
        end
    end
    return (line, lineno)
end

function _load_idle_extensions(self::ConfigManager, sub_section, fp, lineno)::Tuple
    extension_map = get_data(self, "idle extensions")
    if extension_map === nothing
        extension_map = Dict()
    end
    extensions = []
    while true
        line, lineno, bBreak = _readline(self, fp, lineno)
        if bBreak
            break
        end
        line = strip(line)
        if line
            push!(extensions, line)
        end
    end
    extension_map[sub_section+1] = extensions
    _save_data(self, "idle extensions", extension_map)
    return (line, lineno)
end

function test()
    start = clock(time)
    f = "default"
    cm = ConfigManager(f)
    map = get_data(cm, "keys")
    took = clock(time) - start
    @printf("Loaded %s items in %.4f secs", (length(map), took))
end

function main()
    test()
end

main()
end
