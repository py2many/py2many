
using win32com_.client.gencache: EnsureDispatch
using win32com_.client.dynamic: DumbDispatch
import win32com_.test.util
abstract type AbstractRegexTest <: Abstractwin32com_.test.util.TestCase end
mutable struct RegexTest <: AbstractRegexTest
end
function _CheckMatches(self::RegexTest, match, expected)
    found = []
    for imatch in match
        push!(found, imatch.FirstIndex)
    end
    assertEqual(self, collect(found), collect(expected))
end

function _TestVBScriptRegex(self::RegexTest, re)
    StringToSearch = "Python python pYthon Python"
    re.Pattern = "Python"
    re.Global = true
    re.IgnoreCase = true
    match = Execute(re, StringToSearch)
    expected = (0, 7, 14, 21)
    _CheckMatches(self, match, expected)
    re.IgnoreCase = false
    match = Execute(re, StringToSearch)
    expected = (0, 21)
    _CheckMatches(self, match, expected)
end

function testDynamic(self::RegexTest)
    re = DumbDispatch("VBScript.Regexp")
    _TestVBScriptRegex(self, re)
end

function testGenerated(self::RegexTest)
    re = EnsureDispatch("VBScript.Regexp")
    _TestVBScriptRegex(self, re)
end

if abspath(PROGRAM_FILE) == @__FILE__
end
