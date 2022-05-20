using PyCall
win32api = pyimport("win32api")
import win32process
import _thread
import win32trace
import win32event
using win32com_.gen_py.framework: winout
abstract type AbstractWindowOutput <: Abstractwinout.WindowOutput end
outputWindow = nothing
function CollectorThread(stopEvent, file)
InitRead(win32trace)
handle = GetHandle(win32trace)
SetThreadPriority(win32process, GetCurrentThread(win32api), win32process.THREAD_PRIORITY_BELOW_NORMAL)
try
while true
rc = WaitForMultipleObjects(win32event, (handle, stopEvent), 0, win32event.INFINITE)
if rc == win32event.WAIT_OBJECT_0
write(file, replace(read(win32trace), "\000", "<null>"))
else
break;
end
end
finally
TermRead(win32trace)
println("Thread dieing")
end
end

mutable struct WindowOutput <: AbstractWindowOutput
hStopThread

            WindowOutput() = begin
                winout.WindowOutput.__init__((self,) + args...)
_thread.start_new(CollectorThread, (hStopThread, self))
                new()
            end
end
function _StopThread(self::WindowOutput)
SetEvent(win32event, self.hStopThread)
self.hStopThread = nothing
end

function Close(self::WindowOutput)
_StopThread(self)
Close(winout.WindowOutput)
return rc
end

function MakeOutputWindow()
global outputWindow
if outputWindow === nothing
title = "Python Trace Collector"
outputWindow = WindowOutput(title, title)
msg = "# This window will display output from any programs that import win32traceutil\n# win32com_ servers registered with \'--debug\' are in this category.\n"
write(outputWindow, msg)
end
write(outputWindow, "")
return outputWindow
end

if abspath(PROGRAM_FILE) == @__FILE__
MakeOutputWindow()
end