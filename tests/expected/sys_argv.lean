set_option linter.unusedVariables false

def main (args : List String) : IO Unit := do
  let a : List String := (["sys_argv"] ++ args)
  let cmd : String := a[0]!
  if cmd == "dart" then
    pure ()
  else
    assert! (cmd.contains "sys_argv")
  if (a).length > 1 then
    IO.println (toString a[1]!)
  else
    IO.println "OK"
