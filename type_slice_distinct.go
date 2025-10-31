package collex

func (slice TypeSlice) Distinct() TypeSlice {
	var uniques TypeSlice
	seen := make(map[Type]bool)
	for _, t := range slice {
		_, ok := seen[t]
		if ok {
			continue
		}
		seen[t] = true
		uniques = append(uniques, t)
	}
	return uniques
}
