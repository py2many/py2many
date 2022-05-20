using PyCall
pythoncom = pyimport("pythoncom")
include("testAccess.jl")
using win32com_.client: Dispatch, DispatchWithEvents, constants

abstract type AbstractADOEvents end
finished = 0
mutable struct ADOEvents <: AbstractADOEvents
end
function OnWillConnect(self::ADOEvents, str, user, pw, opt, sts, cn)
    #= pass =#
end

function OnConnectComplete(self::ADOEvents, error, status, connection)
    println("connection is$(connection)")
    println("Connected to$(Properties(connection, "Data Source"))")
    global finished
    finished = 1
end

function OnCommitTransComplete(self::ADOEvents, pError, adStatus, pConnection)
    #= pass =#
end

function OnInfoMessage(self::ADOEvents, pError, adStatus, pConnection)
    #= pass =#
end

function OnDisconnect(self::ADOEvents, adStatus, pConnection)
    #= pass =#
end

function OnBeginTransComplete(
    self::ADOEvents,
    TransactionLevel,
    pError,
    adStatus,
    pConnection,
)
    #= pass =#
end

function OnRollbackTransComplete(self::ADOEvents, pError, adStatus, pConnection)
    #= pass =#
end

function OnExecuteComplete(
    self::ADOEvents,
    RecordsAffected,
    pError,
    adStatus,
    pCommand,
    pRecordset,
    pConnection,
)
    #= pass =#
end

function OnWillExecute(
    self::ADOEvents,
    Source,
    CursorType,
    LockType,
    Options,
    adStatus,
    pCommand,
    pRecordset,
    pConnection,
)
    #= pass =#
end

function TestConnection(dbname)
    c = DispatchWithEvents("ADODB.Connection", ADOEvents)
    dsn = "Driver={Microsoft Access Driver (*.mdb)};Dbq=%s" % dbname
    user = "system"
    pw = "manager"
    Open(c, dsn, user, pw, constants.adAsyncConnect)
    end_time = clock(time) + 10
    while clock(time) < end_time
        PumpWaitingMessages(pythoncom)
    end
    if !(finished) != 0
        println("XXX - Failed to connect!")
    end
end

function Test()
    try
        GenerateSupport(testAccess)
    catch exn
        if exn isa pythoncom.com_error
            println("*** Can not import the MSAccess type libraries - tests skipped")
            return
        end
    end
    dbname = CreateTestAccessDatabase(testAccess)
    try
        TestConnection(dbname)
    finally
        std::fs::remove_file(dbname)
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    Test()
end
