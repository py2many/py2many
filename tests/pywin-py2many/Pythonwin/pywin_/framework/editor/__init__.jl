using PyCall
win32ui = pyimport("win32ui")
import win32con
defaultCharacterFormat = (-402653169, 0, 200, 0, 0, 0, 49, "Courier New")
function LoadDefaultEditor()
#= pass =#
end

function GetEditorOption(option, defaultValue, min = nothing, max = nothing)
rc = GetProfileVal(win32ui, "Editor", option, defaultValue)
if min != nothing && rc < min
rc = defaultValue
end
if max != nothing && rc > max
rc = defaultValue
end
return rc
end

function SetEditorOption(option, newValue)
WriteProfileVal(win32ui, "Editor", option, newValue)
end

function DeleteEditorOption(option)
try
WriteProfileVal(win32ui, "Editor", option, nothing)
catch exn
if exn isa win32ui.error
#= pass =#
end
end
end

function GetEditorFontOption(option, default = nothing)
if default === nothing
default = defaultCharacterFormat
end
fmt = GetEditorOption(option, "")
if fmt == ""
return default
end
try
return eval(fmt)
catch exn
println("WARNING: Invalid font setting in registry - setting ignored")
return default
end
end

function SetEditorFontOption(option, newValue)
SetEditorOption(option, string(newValue))
end

using win32com_.gen_py.framework.editor.color.coloreditor: editorTemplate