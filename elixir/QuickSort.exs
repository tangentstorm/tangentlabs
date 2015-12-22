defmodule QuickSort do

  @doc "return a random 32-bit integer"
  def rand, do: round(:rand.uniform(round(:math.pow(2,31))) - :math.pow(2,30))

  @doc "return a list of n random 32-bit integers"
  def rand_nums(0) do [] end
  def rand_nums(n) when n < 0 do raise "rand_nums expects a positive number" end
  def rand_nums(n) do for _ <- 1..n do rand end end

  @doc "perform (something like) a quicksort."
  def qsort([]) do [] end
  def qsort([x|xs]) do
    Enum.concat [qsort(for lo <- xs, lo <  x, do: lo),
                 [x],
                 qsort(for hi <- xs, hi >= x, do: hi)]
  end

  @doc "a distributed version of qsort."
  def dsort([]) do [] end
  def dsort([x|xs]) do
    ltx = Task.async QuickSort, :dsort, [(for lo <- xs, lo <  x, do: lo)]
    gtx = Task.async QuickSort, :dsort, [(for hi <- xs, hi >= x, do: hi)]
    Enum.concat [Task.await(ltx), [x], Task.await(gtx)]
  end

end

# IO.inspect QuickSort.dsort(QuickSort.rand_nums(100000))
