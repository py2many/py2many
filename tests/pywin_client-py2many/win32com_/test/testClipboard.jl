module testClipboard
using PyCall
using Test
pythoncom = pyimport("pythoncom")
using win32com.test: util


import win32con
import winerror
import win32clipboard
using win32com.server.util: NewEnum, wrap
using win32com.server.exception: COMException
abstract type AbstractTestDataObject end
abstract type AbstractClipboardTester end
IDataObject_Methods = split("GetData GetDataHere QueryGetData\n                         GetCanonicalFormatEtc SetData EnumFormatEtc\n                         DAdvise DUnadvise EnumDAdvise")
num_do_objects = 0
function WrapCOMObject(ob, iid = nothing)
return wrap(ob, iid, 0)
end

mutable struct TestDataObject <: AbstractTestDataObject
bytesval::Any
_com_interfaces_::Vector
_public_methods_::Any
supported_fe::Vector

            TestDataObject(bytesval, _com_interfaces_::Vector = [IID_IDataObject(pythoncom)], _public_methods_ = IDataObject_Methods, supported_fe::Vector = []) = begin
                global num_do_objects
num_do_objects += 1
for cf in (win32con.CF_TEXT, win32con.CF_UNICODETEXT)
fe = (cf, nothing, pythoncom.DVASPECT_CONTENT, -1, pythoncom.TYMED_HGLOBAL)
self.supported_fe.append(fe)
end
                new(bytesval, _com_interfaces_, _public_methods_ , supported_fe)
            end
end
function __del__(self::TestDataObject)
global num_do_objects
num_do_objects -= 1
end

function _query_interface_(self::TestDataObject, iid)
if iid == IID_IEnumFORMATETC(pythoncom)
return NewEnum(self.supported_fe, iid)
end
end

function GetData(self::TestDataObject, fe)
ret_stg = nothing
cf, target, aspect, index, tymed = fe
if aspect & DVASPECT_CONTENT(pythoncom) && tymed == TYMED_HGLOBAL(pythoncom)
if cf == win32con.CF_TEXT
ret_stg = STGMEDIUM(pythoncom)
set(ret_stg, TYMED_HGLOBAL(pythoncom), self.bytesval)
elseif cf == win32con.CF_UNICODETEXT
ret_stg = STGMEDIUM(pythoncom)
set(ret_stg, TYMED_HGLOBAL(pythoncom), decode(self.bytesval, "latin1"))
end
end
if ret_stg === nothing
throw(COMException(winerror.E_NOTIMPL))
end
return ret_stg
end

function GetDataHere(self::TestDataObject, fe)
throw(COMException(winerror.E_NOTIMPL))
end

function QueryGetData(self::TestDataObject, fe)
cf, target, aspect, index, tymed = fe
if (aspect & DVASPECT_CONTENT(pythoncom)) == 0
throw(COMException(winerror.DV_E_DVASPECT))
end
if tymed != TYMED_HGLOBAL(pythoncom)
throw(COMException(winerror.DV_E_TYMED))
end
return nothing
end

function GetCanonicalFormatEtc(self::TestDataObject, fe)
RaiseCOMException(winerror.DATA_S_SAMEFORMATETC)
end

function SetData(self::TestDataObject, fe, medium)
throw(COMException(winerror.E_NOTIMPL))
end

function EnumFormatEtc(self::TestDataObject, direction)
if direction != DATADIR_GET(pythoncom)
throw(COMException(winerror.E_NOTIMPL))
end
return NewEnum(self.supported_fe, IID_IEnumFORMATETC(pythoncom))
end

function DAdvise(self::TestDataObject, fe, flags, sink)
throw(COMException(winerror.E_NOTIMPL))
end

function DUnadvise(self::TestDataObject, connection)
throw(COMException(winerror.E_NOTIMPL))
end

function EnumDAdvise(self::TestDataObject)
throw(COMException(winerror.E_NOTIMPL))
end

mutable struct ClipboardTester <: AbstractClipboardTester

end
function setUp(self::ClipboardTester)
OleInitialize(pythoncom)
end

function tearDown(self::ClipboardTester)
try
OleFlushClipboard(pythoncom)
catch exn
if exn isa com_error(pythoncom)
#= pass =#
end
end
end

function testIsCurrentClipboard(self::ClipboardTester)
do_ = TestDataObject(b"Hello from Python")
do_ = WrapCOMObject(do_)
OleSetClipboard(pythoncom, do_)
@test OleIsCurrentClipboard(pythoncom, do_)
end

function testComToWin32(self::ClipboardTester)
do_ = TestDataObject(b"Hello from Python")
do_ = WrapCOMObject(do_)
OleSetClipboard(pythoncom, do_)
OpenClipboard(win32clipboard)
got = GetClipboardData(win32clipboard, win32con.CF_TEXT)
expected = b"Hello from Python"
@test (got == expected)
got = GetClipboardData(win32clipboard, win32con.CF_UNICODETEXT)
@test (got == "Hello from Python")
CloseClipboard(win32clipboard)
end

function testWin32ToCom(self::ClipboardTester)
val = b"Hello again!"
OpenClipboard(win32clipboard)
SetClipboardData(win32clipboard, win32con.CF_TEXT, val)
CloseClipboard(win32clipboard)
do_ = OleGetClipboard(pythoncom)
cf = (win32con.CF_TEXT, nothing, DVASPECT_CONTENT(pythoncom), -1, TYMED_HGLOBAL(pythoncom))
stg = GetData(do_, cf)
got = data(stg)
@test got
end

function testDataObjectFlush(self::ClipboardTester)
do_ = TestDataObject(b"Hello from Python")
do_ = WrapCOMObject(do_)
OleSetClipboard(pythoncom, do_)
@test (num_do_objects == 1)
do_ = nothing
OleFlushClipboard(pythoncom)
@test (num_do_objects == 0)
end

function testDataObjectReset(self::ClipboardTester)
do_ = TestDataObject(b"Hello from Python")
do_ = WrapCOMObject(do_)
OleSetClipboard(pythoncom, do_)
do_ = nothing
@test (num_do_objects == 1)
OleSetClipboard(pythoncom, nothing)
@test (num_do_objects == 0)
end

function main()
testmain(util)
clipboard_tester = ClipboardTester()
setUp(clipboard_tester)
tearDown(clipboard_tester)
testIsCurrentClipboard(clipboard_tester)
testComToWin32(clipboard_tester)
testWin32ToCom(clipboard_tester)
testDataObjectFlush(clipboard_tester)
testDataObjectReset(clipboard_tester)
end

main()
end