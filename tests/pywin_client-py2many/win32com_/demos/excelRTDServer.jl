module excelRTDServer
#= Excel IRTDServer implementation.

This module is a functional example of how to implement the IRTDServer interface
in python, using the pywin32 extensions. Further details, about this interface
and it can be found at:
     http://msdn.microsoft.com/library/default.asp?url=/library/en-us/dnexcl2k2/html/odc_xlrtdfaq.asp
 =#
using PyCall
pythoncom = pyimport("pythoncom")
datetime = pyimport("datetime")
import win32com.server.register

import win32com.client
using win32com: universal
using win32com.client: gencache
using win32com.server.exception: COMException
import threading

abstract type AbstractExcelRTDServer <: Abstractobject end
abstract type AbstractRTDTopic <: Abstractobject end
abstract type AbstractTimeServer <: AbstractExcelRTDServer end
abstract type AbstractTimeTopic <: AbstractRTDTopic end
EXCEL_TLB_GUID = "{00020813-0000-0000-C000-000000000046}"
EXCEL_TLB_LCID = 0
EXCEL_TLB_MAJOR = 1
EXCEL_TLB_MINOR = 4
EnsureModule(gencache, EXCEL_TLB_GUID, EXCEL_TLB_LCID, EXCEL_TLB_MAJOR, EXCEL_TLB_MINOR)
RegisterInterfaces(
    universal,
    EXCEL_TLB_GUID,
    EXCEL_TLB_LCID,
    EXCEL_TLB_MAJOR,
    EXCEL_TLB_MINOR,
    ["IRtdServer", "IRTDUpdateEvent"],
)
mutable struct ExcelRTDServer <: AbstractExcelRTDServer
    #= Base RTDServer class.

        Provides most of the features needed to implement the IRtdServer interface.
        Manages topic adding, removal, and packing up the values for excel.

        Shouldn't be instanciated directly.

        Instead, descendant classes should override the CreateTopic() method.
        Topic objects only need to provide a GetValue() function to play nice here.
        The values given need to be atomic (eg. string, int, float... etc).

        Also note: nothing has been done within this class to ensure that we get
        time to check our topics for updates. I've left that up to the subclass
        since the ways, and needs, of refreshing your topics will vary greatly. For
        example, the sample implementation uses a timer thread to wake itself up.
        Whichever way you choose to do it, your class needs to be able to wake up
        occaisionally, since excel will never call your class without being asked to
        first.

        Excel will communicate with our object in this order:
          1. Excel instanciates our object and calls ServerStart, providing us with
             an IRTDUpdateEvent callback object.
          2. Excel calls ConnectData when it wants to subscribe to a new "topic".
          3. When we have new data to provide, we call the UpdateNotify method of the
             callback object we were given.
          4. Excel calls our RefreshData method, and receives a 2d SafeArray (row-major)
             containing the Topic ids in the 1st dim, and the topic values in the
             2nd dim.
          5. When not needed anymore, Excel will call our DisconnectData to
             unsubscribe from a topic.
          6. When there are no more topics left, Excel will call our ServerTerminate
             method to kill us.

        Throughout, at undetermined periods, Excel will call our Heartbeat
        method to see if we're still alive. It must return a non-zero value, or
        we'll be killed.

        NOTE: By default, excel will at most call RefreshData once every 2 seconds.
              This is a setting that needs to be changed excel-side. To change this,
              you can set the throttle interval like this in the excel VBA object model:
                Application.RTD.ThrottleInterval = 1000 ' milliseconds
         =#
    ALIVE::Int64
    IsAlive::AbstractExcelRTDServer
    NOT_ALIVE::Int64
    __callback::Any
    _com_interfaces_::Vector{String}
    _public_methods_::Vector{String}
    _reg_clsctx_::Any
    topics::Dict

    ExcelRTDServer(
        ALIVE::Int64 = 1,
        IsAlive::AbstractExcelRTDServer = self.ALIVE,
        NOT_ALIVE::Int64 = 0,
        __callback = nothing,
        _com_interfaces_::Vector{String} = ["IRtdServer"],
        _public_methods_::Vector{String} = [
            "ConnectData",
            "DisconnectData",
            "Heartbeat",
            "RefreshData",
            "ServerStart",
            "ServerTerminate",
        ],
        _reg_clsctx_ = CLSCTX_INPROC_SERVER(pythoncom),
        topics::Dict = Dict(),
    ) = begin
        super(ExcelRTDServer, self).__init__()
        new(
            ALIVE,
            IsAlive,
            NOT_ALIVE,
            __callback,
            _com_interfaces_,
            _public_methods_,
            _reg_clsctx_,
            topics,
        )
    end
end
function SignalExcel(self::ExcelRTDServer)
    #= Use the callback we were given to tell excel new data is available. =#
    if self.__callback === nothing
        throw(COMException("Callback excel provided is Null"))
    end
    UpdateNotify(self.__callback)
end

function ConnectData(self::ExcelRTDServer, TopicID, Strings, GetNewValues)::Tuple
    #= Creates a new topic out of the Strings excel gives us. =#
    try
        self.topics[TopicID+1] = CreateTopic(self, Strings)
    catch exn
        let why = exn
            if why isa Exception
                throw(COMException(string(why)))
            end
        end
    end
    GetNewValues = true
    result = self.topics[TopicID+1]
    if result === nothing
        result = "# %s: Waiting for update" % self.__class__.__name__
    else
        result = GetValue(result)
    end
    OnConnectData(self, TopicID)
    return (result, GetNewValues)
end

function DisconnectData(self::ExcelRTDServer, TopicID)
    #= Deletes the given topic. =#
    OnDisconnectData(self, TopicID)
    if TopicID in self.topics
        self.topics[TopicID+1] = nothing
        #Delete Unsupported
        del(self.topics)
    end
end

function Heartbeat(self::ExcelRTDServer)::ExcelRTDServer
    #= Called by excel to see if we're still here. =#
    return self.IsAlive
end

function RefreshData(self::ExcelRTDServer, TopicCount)::Tuple
    #= Packs up the topic values. Called by excel when it's ready for an update.

            Needs to:
              * Return the current number of topics, via the "ByRef" TopicCount
              * Return a 2d SafeArray of the topic data.
                - 1st dim: topic numbers
                - 2nd dim: topic values

            We could do some caching, instead of repacking everytime...
            But this works for demonstration purposes. =#
    TopicCount = length(self.topics)
    OnRefreshData(self)
    results = [[nothing] * TopicCount, [nothing] * TopicCount]
    for (idx, topicdata) in enumerate(items(self.topics))
        topicNum, topic = topicdata
        results[1][idx+1] = topicNum
        results[2][idx+1] = GetValue(topic)
    end
    return (tuple(results), TopicCount)
end

function ServerStart(self::ExcelRTDServer, CallbackObject)::ExcelRTDServer
    #= Excel has just created us... We take its callback for later, and set up shop. =#
    self.IsAlive = self.ALIVE
    if CallbackObject === nothing
        throw(COMException("Excel did not provide a callback"))
    end
    IRTDUpdateEventKlass =
        GetClass(win32com.client.CLSIDToClass, "{A43788C1-D91B-11D3-8F39-00C04F3651B8}")
    self.__callback = IRTDUpdateEventKlass(CallbackObject)
    OnServerStart(self)
    return self.IsAlive
end

function ServerTerminate(self::ExcelRTDServer)
    #= Called when excel no longer wants us. =#
    self.IsAlive = self.NOT_ALIVE
    OnServerTerminate(self)
end

function CreateTopic(self::ExcelRTDServer, TopicStrings = nothing)
    #= Topic factory method. Subclass must override.

            Topic objects need to provide:
              * GetValue() method which returns an atomic value.

            Will raise NotImplemented if not overridden.
             =#
    throw(NotImplemented("Subclass must implement"))
end

function OnConnectData(self::ExcelRTDServer, TopicID)
    #= Called when a new topic has been created, at excel's request. =#
    #= pass =#
end

function OnDisconnectData(self::ExcelRTDServer, TopicID)
    #= Called when a topic is about to be deleted, at excel's request. =#
    #= pass =#
end

function OnRefreshData(self::ExcelRTDServer)
    #= Called when excel has requested all current topic data. =#
    #= pass =#
end

function OnServerStart(self::ExcelRTDServer)
    #= Called when excel has instanciated us. =#
    #= pass =#
end

function OnServerTerminate(self::ExcelRTDServer)
    #= Called when excel is about to destroy us. =#
    #= pass =#
end

mutable struct RTDTopic <: AbstractRTDTopic
    #= Base RTD Topic.
        Only method required by our RTDServer implementation is GetValue().
        The others are more for convenience. =#
    TopicStrings::Any
    __currentValue::Any
    __dirty::Bool

    RTDTopic(TopicStrings, __currentValue = nothing, __dirty::Bool = false) = begin
        super(RTDTopic, self).__init__()
        new(TopicStrings, __currentValue, __dirty)
    end
end
function Update(self::RTDTopic, sender)
    #= Called by the RTD Server.
            Gives us a chance to check if our topic data needs to be
            changed (eg. check a file, quiz a database, etc). =#
    throw(NotImplemented("subclass must implement"))
end

function Reset(self::RTDTopic)
    #= Call when this topic isn't considered "dirty" anymore. =#
    self.__dirty = false
end

function GetValue(self::RTDTopic)::RTDTopic
    return self.__currentValue
end

function SetValue(self::RTDTopic, value)
    self.__dirty = true
    self.__currentValue = value
end

function HasChanged(self::RTDTopic)::RTDTopic
    return self.__dirty
end

mutable struct TimeServer <: AbstractTimeServer
    #= Example Time RTD server.

        Sends time updates back to excel.

        example of use, in an excel sheet:
          =RTD("Python.RTD.TimeServer","","seconds","5")

        This will cause a timestamp string to fill the cell, and update its value
        every 5 seconds (or as close as possible depending on how busy excel is).

        The empty string parameter denotes the com server is running on the local
        machine. Otherwise, put in the hostname to look on. For more info
        on this, lookup the Excel help for its "RTD" worksheet function.

        Obviously, you'd want to wrap this kind of thing in a friendlier VBA
        function.

        Also, remember that the RTD function accepts a maximum of 28 arguments!
        If you want to pass more, you may need to concatenate arguments into one
        string, and have your topic parse them appropriately.
         =#
    topics::Any
    INTERVAL::Float64
    _reg_clsid_::String
    _reg_desc_::String
    _reg_progid_::String
    ticker::Any

    TimeServer(
        INTERVAL::Float64 = 0.5,
        _reg_clsid_::String = "{EA7F2CF1-11A2-45E4-B2D5-68E240DB8CB1}",
        _reg_desc_::String = "Python class implementing Excel IRTDServer -- feeds time",
        _reg_progid_::String = "Python.RTD.TimeServer",
        ticker = Timer(threading, self.INTERVAL, self.Update),
    ) = begin
        super(TimeServer, self).__init__()
        new(INTERVAL, _reg_clsid_, _reg_desc_, _reg_progid_, ticker)
    end
end
function OnServerStart(self::TimeServer)
    start(self.ticker)
end

function OnServerTerminate(self::TimeServer)
    if !isSet(self.ticker.finished)
        cancel(self.ticker)
    end
end

function Update(self::TimeServer)
    self.ticker = Timer(threading, self.INTERVAL, self.Update)
    try
        if length(self.topics) != 0
            refresh = false
            for topic in values(self.topics)
                Update(topic)
                if HasChanged(topic)
                    refresh = true
                end
                Reset(topic)
            end
            if refresh
                SignalExcel(self)
            end
        end
    finally
        start(self.ticker)
    end
end

function CreateTopic(self::TimeServer, TopicStrings = nothing)::TimeTopic
    #= Topic factory. Builds a TimeTopic object out of the given TopicStrings. =#
    return TimeTopic(TopicStrings)
end

mutable struct TimeTopic <: AbstractTimeTopic
    #= Example topic for example RTD server.

        Will accept some simple commands to alter how long to delay value updates.

        Commands:
          * seconds, delay_in_seconds
          * minutes, delay_in_minutes
          * hours, delay_in_hours
         =#
    cmd::Any
    checkpoint::Any
    delay::Float64

    TimeTopic(
        TopicStrings,
        checkpoint = timestamp(self),
        delay::Float64 = float(self.delay),
    ) = begin
        super(TimeTopic, self).__init__(TopicStrings)
        try
            self.cmd, self.delay = self.TopicStrings
        catch exn
            let E = exn
                if E isa Exception
                    throw(ValueError("Invalid topic strings: %s" % string(TopicStrings)))
                end
            end
        end
        self.SetValue(string(self.checkpoint))
        new(TopicStrings, checkpoint, delay)
    end
end
function timestamp(self::TimeTopic)
    return now(datetime.datetime)
end

function Update(self::TimeTopic, sender)
    now = timestamp(self)
    delta = now - self.checkpoint
    refresh = false
    if self.cmd == "seconds"
        if seconds(delta) >= self.delay
            refresh = true
        end
    elseif self.cmd == "minutes"
        if minutes(delta) >= self.delay
            refresh = true
        end
    elseif self.cmd == "hours"
        if hours(delta) >= self.delay
            refresh = true
        end
    else
        SetValue(self, "#Unknown command: " + self.cmd)
    end
    if refresh
        SetValue(self, string(now))
        self.checkpoint = now
    end
end

function main()
    UseCommandLine(win32com.server.register, TimeServer)
end

main()
end
