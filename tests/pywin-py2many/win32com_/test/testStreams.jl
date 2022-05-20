using PyCall
pythoncom = pyimport("pythoncom")

import win32com_.server.util
import win32com_.test.util

using pywin32_testutil: str2bytes
abstract type AbstractPersists end
abstract type AbstractStream end
abstract type AbstractBadStream <: AbstractStream end
abstract type AbstractStreamTest <: Abstractwin32com_.test.util.TestCase end
mutable struct Persists <: AbstractPersists
    data
    dirty::Int64
    _com_interfaces_::Vector
    _public_methods_::Vector{String}

    Persists(
        data,
        dirty::Int64,
        _com_interfaces_::Vector = [pythoncom.IID_IPersistStreamInit],
        _public_methods_::Vector{String} = [
            "GetClassID",
            "IsDirty",
            "Load",
            "Save",
            "GetSizeMax",
            "InitNew",
        ],
    ) = new(data, dirty, _com_interfaces_, _public_methods_)
end
function GetClassID(self::Persists)
    return pythoncom.IID_NULL
end

function IsDirty(self::Persists)::Int64
    return self.dirty
end

function Load(self::Persists, stream)
    self.data = Read(stream, 26)
end

function Save(self::Persists, stream, clearDirty)
    Write(stream, self.data)
    if clearDirty
        self.dirty = 0
    end
end

function GetSizeMax(self::Persists)::Int64
    return 1024
end

function InitNew(self::Persists)
    #= pass =#
end

mutable struct Stream <: AbstractStream
    data
    index::Int64
    _com_interfaces_::Vector
    _public_methods_::Vector{String}

    Stream(
        data,
        index::Int64,
        _com_interfaces_::Vector = [pythoncom.IID_IStream],
        _public_methods_::Vector{String} = ["Read", "Write", "Seek"],
    ) = new(data, index, _com_interfaces_, _public_methods_)
end
function Read(self::Stream, amount)
    result = self.data[self.index+1:self.index+amount]
    self.index = self.index + amount
    return result
end

function Write(self::Stream, data)::Int64
    self.data = data
    self.index = 0
    return length(data)
end

function Seek(self::Stream, dist, origin)::Int64
    if origin == pythoncom.STREAM_SEEK_SET
        self.index = dist
    elseif origin == pythoncom.STREAM_SEEK_CUR
        self.index = self.index + dist
    elseif origin == pythoncom.STREAM_SEEK_END
        self.index = length(self.data) + dist
    else
        throw(ValueError("Unknown Seek type: " * string(origin)))
    end
    if self.index < 0
        self.index = 0
    else
        self.index = min(self.index, length(self.data))
    end
    return self.index
end

mutable struct BadStream <: AbstractBadStream
    #= PyGStream::Read could formerly overflow buffer if the python implementation
        returned more data than requested.
         =#

end
function Read(self::BadStream, amount)::Int64
    return str2bytes("x") * (amount + 1)
end

mutable struct StreamTest <: AbstractStreamTest
end
function _readWrite(self::StreamTest, data, write_stream, read_stream = nothing)
    if read_stream === nothing
        read_stream = write_stream
    end
    Write(write_stream, data)
    Seek(read_stream, 0, pythoncom.STREAM_SEEK_SET)
    got = Read(read_stream, length(data))
    assertEqual(self, data, got)
    Seek(read_stream, 1, pythoncom.STREAM_SEEK_SET)
    got = Read(read_stream, length(data) - 2)
    assertEqual(self, data[2:-1], got)
end

function testit(self::StreamTest)
    mydata = str2bytes("abcdefghijklmnopqrstuvwxyz")
    s = Stream(mydata)
    p = Persists()
    Load(p, s)
    Save(p, s, 0)
    assertEqual(self, s.data, mydata)
    s2 = wrap(win32com_.server.util, s, pythoncom.IID_IStream)
    p2 = wrap(win32com_.server.util, p, pythoncom.IID_IPersistStreamInit)
    _readWrite(self, mydata, s, s)
    _readWrite(self, mydata, s, s2)
    _readWrite(self, mydata, s2, s)
    _readWrite(self, mydata, s2, s2)
    _readWrite(self, str2bytes("string with\000a NULL"), s2, s2)
    Write(s, mydata)
    Load(p2, s2)
    Save(p2, s2, 0)
    assertEqual(self, s.data, mydata)
end

function testseek(self::StreamTest)
    s = Stream(str2bytes("yo"))
    s = wrap(win32com_.server.util, s, pythoncom.IID_IStream)
    Seek(s, 4294967296, pythoncom.STREAM_SEEK_SET)
end

function testerrors(self::StreamTest)
    records, old_log = setup_test_logger(win32com_.test.util)
    badstream = BadStream("Check for buffer overflow")
    badstream2 = wrap(win32com_.server.util, badstream, pythoncom.IID_IStream)
    assertRaises(self, pythoncom.com_error, badstream2.Read, 10)
    restore_test_logger(win32com_.test.util, old_log)
    assertEqual(self, length(records), 1)
    assertTrue(self, startswith(None.msg, "pythoncom error"))
end

if abspath(PROGRAM_FILE) == @__FILE__
end
