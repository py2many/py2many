#!/usr/bin/env python
import sys
import argparse
import os
import subprocess
from pyrs.transpiler import transpile

                    
def rust_format(file_path):
    result = subprocess.call(['rustfmt', file_path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Transpile Python to Rust")
    parser.add_argument("file", metavar='<python file>')
    args = parser.parse_args()

    if os.path.isfile(args.file):
        source = open(args.file).read()
        rs = transpile(source)
        sys.stdout.write(rs)
    else:
        print("Transpiling whole directiory:")
        basename = os.path.basename(args.file)
        for root, subdir, filenames in os.walk(args.file):
            common_prefix = os.path.commonprefix([args.file, root])
            relpath = os.path.relpath(root, args.file)
            target_root = os.path.join(common_prefix + "-pyrs", relpath)
                
            for relative_path in filenames:
                src_file = os.path.join(root,relative_path)
                basename, extension =  os.path.splitext(relative_path)
                if extension == ".py":
                    dst_file = os.path.join(target_root, basename + ".rs")
                    os.makedirs(os.path.dirname(dst_file), exist_ok=True)
                    try:
                        pysource = open(src_file).read()
                        rs = transpile(pysource)
                        with open(dst_file, "w") as f:
                            f.write(rs)
                        
                        if rust_format(dst_file) != 0:
                            print("Transpiled but not formatted:", dst_file)
                        
                    except Exception as e:
                        print("Error: Could not transpile:", src_file)
                        print("Due to:", e)