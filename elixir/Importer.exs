# experiment to show how 'import' works
# importing a module provides access to
# all of that modules public declarations,
# but does not expose them as public in
# the importing module.

defmodule Imported do
  def foo() do :foo end
end

defmodule Importer do 
  import Imported
  def bar() do ["bar:", foo] end
end

IO.inspect Importer.bar
IO.inspect Importer.foo

# output:
# ---------------------------------------------------------------------------------
# Erlang/OTP 18 [erts-7.2] [source] [64-bit] [async-threads:10] [kernel-poll:false]
# 
# ["bar:", :foo]
# ** (UndefinedFunctionError) undefined function: Importer.foo/0
#     Importer.foo()
#     Importer.exs:14: (file)
#     (elixir) lib/code.ex:363: Code.require_file/2

