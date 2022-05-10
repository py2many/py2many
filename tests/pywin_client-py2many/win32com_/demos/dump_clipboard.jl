module dump_clipboard
using Printf
using PyCall
pythoncom = pyimport("pythoncom")

import win32con
formats = split(
    "CF_TEXT CF_BITMAP CF_METAFILEPICT CF_SYLK CF_DIF CF_TIFF\n            CF_OEMTEXT CF_DIB CF_PALETTE CF_PENDATA CF_RIFF CF_WAVE\n            CF_UNICODETEXT CF_ENHMETAFILE CF_HDROP CF_LOCALE CF_MAX\n            CF_OWNERDISPLAY CF_DSPTEXT CF_DSPBITMAP CF_DSPMETAFILEPICT\n            CF_DSPENHMETAFILE",
)
format_name_map = Dict()
for f in formats
    val = getattr(win32con, f)
    format_name_map[val+1] = f
end
tymeds = [attr for attr in keys(pythoncom.__dict__) if startswith(attr, "TYMED_")]
function DumpClipboard()
    do_ = OleGetClipboard(pythoncom)
    println("Dumping all clipboard formats...")
    for fe in EnumFormatEtc(do_)
        fmt, td, aspect, index, tymed = fe
        tymeds_this =
            [getattr(pythoncom, t) for t in tymeds if tymed & getattr(pythoncom, t)]
        println("Clipboard format", get(format_name_map, fmt, string(fmt)))
        for t_this in tymeds_this
            fetc_query = (fmt, td, aspect, index, t_this)
            try
                QueryGetData(do_, fetc_query)
            catch exn
                if exn isa com_error(pythoncom)
                    println("Eeek - QGD indicated failure for tymed", t_this)
                end
            end
            try
                medium = GetData(do_, fetc_query)
            catch exn
                let exc = exn
                    if exc isa com_error(pythoncom)
                        println("Failed to get the clipboard data:", exc)
                        continue
                    end
                end
            end
            if tymed(medium) == TYMED_GDI(pythoncom)
                data = "GDI handle %d" % data(medium)
            elseif tymed(medium) == TYMED_MFPICT(pythoncom)
                data = "METAFILE handle %d" % data(medium)
            elseif tymed(medium) == TYMED_ENHMF(pythoncom)
                data = "ENHMETAFILE handle %d" % data(medium)
            elseif tymed(medium) == TYMED_HGLOBAL(pythoncom)
                data = "%d bytes via HGLOBAL" % length(data(medium))
            elseif tymed(medium) == TYMED_FILE(pythoncom)
                data = "filename \'%s\'" % data
            elseif tymed(medium) == TYMED_ISTREAM(pythoncom)
                stream = data(medium)
                Seek(stream, 0, 0)
                bytes = 0
                while true
                    chunk = Read(stream, 4096)
                    if !(chunk)
                        break
                    end
                    bytes += length(chunk)
                end
                data = "%d bytes via IStream" % bytes
            elseif tymed(medium) == TYMED_ISTORAGE(pythoncom)
                data = "a IStorage"
            else
                data = "*** unknown tymed!"
            end
            println(" -> got", data)
        end
    end
    do_ = nothing
end

function main()
    DumpClipboard()
    if _GetInterfaceCount(pythoncom) + _GetGatewayCount(pythoncom)
        @printf(
            "XXX - Leaving with %d/%d COM objects alive",
            (_GetInterfaceCount(pythoncom), _GetGatewayCount(pythoncom))
        )
    end
end

main()
end
