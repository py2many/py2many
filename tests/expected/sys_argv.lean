set_option linter.unusedVariables false

def main (args : List String) : IO Unit := do
  let a : List String := (["sys_argv"] ++ args)
  let cmd : String := a[0]!
  if h1 : cmd == "dart" then
    pure ()
  else
    assert! (cmd.contains "sys_argv")
  if h2 : (a).length > 1 then
    IO.println (toString a[1]!)
  else
    IO.println "OK"
