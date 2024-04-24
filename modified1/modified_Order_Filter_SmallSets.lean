def smallSets (l : Filter α) : Filter (Set α) :=
  l.lift' powerset
#align filter.small_sets Filter.smallSets