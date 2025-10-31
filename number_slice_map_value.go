package collex

func (slice NumberSlice) MapValue(fn func(Number) Value) []Value {
	mapped := make([]Value, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice NumberSlice) MapValueAsync(fn func(Number) Value, options ...NumberSliceAsyncOption) []Value {
	output := make([]Value, len(slice))
	eachFn := func(t Number, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.AsyncEachIndex(eachFn, options...)
	return output
}
