import LogicalFoundationsLean

def hello := "world"

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
