using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
include("configui.jl")
import string


using win32com_.gen_py.mfc: docview
import win32com_.gen_py.framework.window

include("frame.jl")
abstract type AbstractEditorTemplateBase <: AbstractParentEditorTemplate end
ParentEditorTemplate = docview.DocTemplate
mutable struct EditorTemplateBase <: AbstractEditorTemplateBase
makeDoc
makeFrame
makeView
res

            EditorTemplateBase(res = win32ui.IDR_TEXTTYPE, makeDoc = nothing, makeFrame = nothing, makeView = nothing) = begin
                if makeFrame === nothing
makeFrame = frame.EditorFrame
end
ParentEditorTemplate.__init__(self, res, makeDoc, makeFrame, makeView)
                new(res , makeDoc , makeFrame , makeView )
            end
end
function _CreateDocTemplate(self::EditorTemplateBase, resourceId)
@assert(0)
end

function CreateWin32uiDocument(self::EditorTemplateBase)
@assert(0)
end

function GetFileExtensions(self::EditorTemplateBase)
return (".txt", ".py")
end

function MatchDocType(self::EditorTemplateBase, fileName, fileType)
doc = FindOpenDocument(self, fileName)
if doc
return doc
end
ext = lower(splitext(os.path, fileName)[2])
if ext ∈ GetFileExtensions(self)
return win32ui.CDocTemplate_Confidence_yesAttemptNative
end
return win32ui.CDocTemplate_Confidence_maybeAttemptForeign
end

function InitialUpdateFrame(self::EditorTemplateBase, frame, doc, makeVisible = 1)
InitialUpdateFrame(self._obj_, frame, doc, makeVisible)
_UpdateUIForState(doc)
end

function GetPythonPropertyPages(self::EditorTemplateBase)::Vector
#= Returns a list of property pages =#
return [EditorPropertyPage(configui), EditorWhitespacePropertyPage(configui)]
end

function OpenDocumentFile(self::EditorTemplateBase, filename, bMakeVisible = 1)
if filename != nothing
try
path = split(os.path, filename)[1]
filename = FindFiles(win32api, filename)[1][9]
filename = join
catch exn
 let details = exn
if details isa (win32api.error, IndexError)
#= pass =#
end
end
end
end
return OpenDocumentFile(self._obj_, filename, bMakeVisible)
end
