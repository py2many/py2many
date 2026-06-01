def main : IO Unit := do
  IO.println "Hello world!"
  IO.println (String.intercalate " " [toString "Hello", toString "world!"])
