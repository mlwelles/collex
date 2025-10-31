package collex

func (slice TypeSlice) MapValue(fn func(Type) Value) []Value {
	mapped := make([]Value, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice TypeSlice) MapValueAsync(fn func(Type) Value) []Value {
	output := make([]Value, len(slice))
	eachFn := func(t Type, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.AsyncEachIndex(eachFn)
	return output

}
