using PyCall
win32ui = pyimport("win32ui")

import win32con
include("object.jl")
include("window.jl")
abstract type AbstractView <: Abstractwindow.Wnd end
abstract type AbstractCtrlView <: AbstractView end
abstract type AbstractEditView <: AbstractCtrlView end
abstract type AbstractRichEditView <: AbstractCtrlView end
abstract type AbstractListView <: AbstractCtrlView end
abstract type AbstractTreeView <: AbstractCtrlView end
abstract type AbstractScrollView <: AbstractView end
abstract type AbstractFormView <: AbstractView end
abstract type AbstractDocument <: Abstractobject.CmdTarget end
abstract type AbstractRichEditDoc <: Abstractobject.CmdTarget end
abstract type AbstractCreateContext end
abstract type AbstractDocTemplate <: Abstractobject.CmdTarget end
abstract type AbstractRichEditDocTemplate <: AbstractDocTemplate end
abstract type AbstractFormTemplate <: AbstractDocTemplate end
mutable struct View <: AbstractView


            View(initobj) = begin
                window.Wnd.__init__(self, initobj)
                new(initobj)
            end
end
function OnInitialUpdate(self::View)
#= pass =#
end

mutable struct CtrlView <: AbstractCtrlView
style::Int64

            CtrlView(doc, wndclass, style = 0) = begin
                View(win32ui.CreateCtrlView(doc, wndclass, style))
                new(doc, wndclass, style )
            end
end

mutable struct EditView <: AbstractEditView


            EditView(doc) = begin
                View(win32ui.CreateEditView(doc))
                new(doc)
            end
end

mutable struct RichEditView <: AbstractRichEditView


            RichEditView(doc) = begin
                View(win32ui.CreateRichEditView(doc))
                new(doc)
            end
end

mutable struct ListView <: AbstractListView


            ListView(doc) = begin
                View(win32ui.CreateListView(doc))
                new(doc)
            end
end

mutable struct TreeView <: AbstractTreeView


            TreeView(doc) = begin
                View(win32ui.CreateTreeView(doc))
                new(doc)
            end
end

mutable struct ScrollView <: AbstractScrollView


            ScrollView(doc) = begin
                View(win32ui.CreateView(doc))
                new(doc)
            end
end

mutable struct FormView <: AbstractFormView


            FormView(doc, id) = begin
                View(win32ui.CreateFormView(doc, id))
                new(doc, id)
            end
end

mutable struct Document <: AbstractDocument
docobj

            Document(template, docobj = nothing) = begin
                if docobj === nothing
docobj = template.DoCreateDoc()
end
object.CmdTarget.__init__(self, docobj)
                new(template, docobj )
            end
end

mutable struct RichEditDoc <: AbstractRichEditDoc


            RichEditDoc(template) = begin
                object.CmdTarget.__init__(self, template.DoCreateRichEditDoc())
                new(template)
            end
end

mutable struct CreateContext <: AbstractCreateContext
#= A transient base class used as a CreateContext =#
template
doc
end
function __del__(self::CreateContext)
close(self)
end

function close(self::CreateContext)
self.doc = nothing
self.template = nothing
end

mutable struct DocTemplate <: AbstractDocTemplate
MakeDocument
MakeFrame
MakeView
resourceId

            DocTemplate(resourceId = nothing, MakeDocument = nothing, MakeFrame = nothing, MakeView = nothing) = begin
                if resourceId === nothing
resourceId = win32ui.IDR_PYTHONTYPE
end
object.CmdTarget.__init__(self, _CreateDocTemplate(resourceId))
_SetupSharedMenu_()
                new(resourceId , MakeDocument , MakeFrame , MakeView )
            end
end
function _SetupSharedMenu_(self::DocTemplate)
#= pass =#
end

function _CreateDocTemplate(self::DocTemplate, resourceId)
return CreateDocTemplate(win32ui, resourceId)
end

function __del__(self::DocTemplate)
__del__(object.CmdTarget)
end

function CreateCreateContext(self::DocTemplate, doc = nothing)::CreateContext
return CreateContext(self, doc)
end

function CreateNewFrame(self::DocTemplate, doc)
makeFrame = self.MakeFrame
if makeFrame === nothing
makeFrame = window.MDIChildWnd
end
wnd = makeFrame()
context = CreateCreateContext(self, doc)
LoadFrame(wnd, GetResourceID(self), -1, nothing, context)
return wnd
end

function CreateNewDocument(self::DocTemplate)
makeDocument = self.MakeDocument
if makeDocument === nothing
makeDocument = Document
end
return makeDocument(self)
end

function CreateView(self::DocTemplate, frame, context)
makeView = self.MakeView
if makeView === nothing
makeView = EditView
end
view = makeView(context.doc)
CreateWindow(view, frame)
end

mutable struct RichEditDocTemplate <: AbstractRichEditDocTemplate
MakeDocument
MakeFrame
MakeView
resourceId

            RichEditDocTemplate(resourceId = nothing, MakeDocument = nothing, MakeFrame = nothing, MakeView = nothing) = begin
                if MakeView === nothing
MakeView = RichEditView
end
if MakeDocument === nothing
MakeDocument = RichEditDoc
end
DocTemplate(resourceId, MakeDocument, MakeFrame, MakeView)
                new(resourceId , MakeDocument , MakeFrame , MakeView )
            end
end
function _CreateDocTemplate(self::RichEditDocTemplate, resourceId)
return CreateRichEditDocTemplate(win32ui, resourceId)
end

function t()
mutable struct FormTemplate <: AbstractFormTemplate

end
function CreateView(self::FormTemplate, frame, context)
makeView = self.MakeView
view = ListView(context.doc)
CreateWindow(view, frame)
end

t = FormTemplate()
return OpenDocumentFile(t, nothing)
end
