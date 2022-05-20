using Printf

import tempfile

import win32com_.test.util
abstract type AbstractXSLT <: Abstractwin32com_.test.util.TestCase end
expected_output = "The jscript test worked.\nThe Python test worked"
mutable struct XSLT <: AbstractXSLT
end
function testAll(self::XSLT)
    output_name = mktemp(tempfile, "-pycom-test")
    cmd = "cscript //nologo testxslt.js doesnt_matter.xml testxslt.xsl " + output_name
    ExecuteShellCommand(win32com_.test.util, cmd, self)
    try
        f = open(output_name)
        try
            got = read(f)
            if got != expected_output
                @printf("ERROR: XSLT expected output of %r\n", expected_output)
                @printf("but got %r\n", got)
            end
        finally
            close(f)
        end
    finally
        try
            std::fs::remove_file(output_name)
        catch exn
            if exn isa os.error
                #= pass =#
            end
        end
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
end
