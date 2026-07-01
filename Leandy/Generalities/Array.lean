def Array.first? {α} (arr: Array α) (deflt : α) :=
  if h: arr.size > 0 then arr[0] else deflt
