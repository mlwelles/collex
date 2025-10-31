package collex

func (slice BoolSlice) AllTrue() bool {
	return slice.All(func(b bool) bool { return b })
}

func (slice BoolSlice) AllFalse() bool {
	return slice.All(func(b bool) bool { return !b })
}

func (slice BoolSlice) AnyTrue() bool {
	return slice.Any(func(b bool) bool { return b })
}

func (slice BoolSlice) AnyFalse() bool {
	return slice.Any(func(b bool) bool { return !b })
}
