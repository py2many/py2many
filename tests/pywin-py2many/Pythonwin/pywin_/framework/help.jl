using OrderedCollections
using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import win32help
import winerror
using win32com_.gen_py.dialogs: list

import win32con

import string

import regutil

htmlhelp_handle = nothing
html_help_command_translators = Dict(
    win32con.HELP_CONTENTS => 1,
    win32con.HELP_CONTEXT => 15,
    win32con.HELP_FINDER => 1,
)
function FinalizeHelp()
    global htmlhelp_handle
    if htmlhelp_handle != nothing
        try
            frame = 0
            HtmlHelp(win32help, frame, nothing, win32help.HH_UNINITIALIZE, htmlhelp_handle)
        catch exn
            if exn isa win32help.error
                println("Failed to finalize htmlhelp!")
            end
        end
        htmlhelp_handle = nothing
    end
end

function OpenHelpFile(fileName, helpCmd = nothing, helpArg = nothing)
    #= Open a help file, given a full path =#
    DoWaitCursor(win32ui, 1)
    try
        if helpCmd === nothing
            helpCmd = win32con.HELP_CONTENTS
        end
        ext = lower(splitext(os.path, fileName)[2])
        if ext == ".hlp"
            WinHelp(
                win32api,
                GetSafeHwnd(GetMainFrame(win32ui)),
                fileName,
                helpCmd,
                helpArg,
            )
        elseif 0 && ext == ".chm"
            global htmlhelp_handle
            helpCmd = get(html_help_command_translators, helpCmd, helpCmd)
            frame = 0
            if htmlhelp_handle === nothing
                htmlhelp_hwnd, htmlhelp_handle =
                    HtmlHelp(win32help, frame, nothing, win32help.HH_INITIALIZE)
            end
            HtmlHelp(win32help, frame, fileName, helpCmd, helpArg)
        else
            ShellExecute(win32api, 0, "open", fileName, nothing, "", win32con.SW_SHOW)
        end
        return fileName
    finally
        DoWaitCursor(win32ui, -1)
    end
end

function ListAllHelpFiles()::Vector
    ret = []
    ret = _ListAllHelpFilesInRoot(win32con.HKEY_LOCAL_MACHINE)
    for item in _ListAllHelpFilesInRoot(win32con.HKEY_CURRENT_USER)
        if item ∉ ret
            push!(ret, item)
        end
    end
    return ret
end

function _ListAllHelpFilesInRoot(root)::Vector
    #= Returns a list of (helpDesc, helpFname) for all registered help files =#
    retList = []
    try
        key = RegOpenKey(
            win32api,
            root,
            BuildDefaultPythonKey(regutil) + "\\Help",
            0,
            win32con.KEY_READ,
        )
    catch exn
        let exc = exn
            if exc isa win32api.error
                if exc.winerror != winerror.ERROR_FILE_NOT_FOUND
                    error()
                end
                return retList
            end
        end
    end
    try
        keyNo = 0
        while true
            try
                helpDesc = RegEnumKey(win32api, key, keyNo)
                helpFile = RegQueryValue(win32api, key, helpDesc)
                push!(retList, (helpDesc, helpFile))
                keyNo = keyNo + 1
            catch exn
                let exc = exn
                    if exc isa win32api.error
                        if exc.winerror != winerror.ERROR_NO_MORE_ITEMS
                            error()
                        end
                        break
                    end
                end
            end
        end
    finally
        RegCloseKey(win32api, key)
    end
    return retList
end

function SelectAndRunHelpFile()
    helpFiles = ListAllHelpFiles()
    if length(helpFiles) == 1
        index = 0
    else
        index = SelectFromLists(list, "Select Help file", helpFiles, ["Title"])
    end
    if index != nothing
        OpenHelpFile(helpFiles[index+1][2])
    end
end

helpIDMap = nothing
function SetHelpMenuOtherHelp(mainMenu)
    #= Modifies the main Help Menu to handle all registered help files.
        mainMenu -- The main menu to modify - usually from docTemplate.GetSharedMenu()
         =#
    global helpIDMap
    if helpIDMap === nothing
        helpIDMap = OrderedDict()
        cmdID = win32ui.ID_HELP_OTHER
        excludeList = ["Main Python Documentation", "Pythonwin Reference"]
        firstList = ListAllHelpFiles()
        excludeFnames = []
        for (desc, fname) in firstList
            if desc ∈ excludeList
                push!(excludeFnames, fname)
            end
        end
        helpDescs = []
        for (desc, fname) in firstList
            if fname ∉ excludeFnames
                helpIDMap[cmdID] = (desc, fname)
                HookCommand(GetMainFrame(win32ui), HandleHelpOtherCommand, cmdID)
                cmdID = cmdID + 1
            end
        end
    end
    helpMenu = GetSubMenu(mainMenu, GetMenuItemCount(mainMenu) - 1)
    otherHelpMenuPos = 2
    otherMenu = GetSubMenu(helpMenu, otherHelpMenuPos)
    while GetMenuItemCount(otherMenu)
        DeleteMenu(otherMenu, 0, win32con.MF_BYPOSITION)
    end
    if helpIDMap
        for (id, (desc, fname)) in items(helpIDMap)
            AppendMenu(otherMenu, win32con.MF_ENABLED | win32con.MF_STRING, id, desc)
        end
    else
        EnableMenuItem(
            helpMenu,
            otherHelpMenuPos,
            win32con.MF_BYPOSITION | win32con.MF_GRAYED,
        )
    end
end

function HandleHelpOtherCommand(cmd, code)
    OpenHelpFile(helpIDMap[cmd+1][2])
end
