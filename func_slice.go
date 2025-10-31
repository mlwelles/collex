package collex

import (
	"errors"
	"math/rand"
	"runtime"
)

type FuncSlice []Func
type FuncSliceReduceOption func(*FuncSliceReduceOptions)
type FuncSliceReduceOptions struct {
	initial Func
}

type FuncSliceAsyncOption func(options *FuncSliceAsyncOptions)
type FuncSliceAsyncOptions struct {
	PoolSize int
}

func WithFuncAsyncPoolSize(size int) FuncSliceAsyncOption {
	return func(options *FuncSliceAsyncOptions) {
		options.PoolSize = size
	}
}

func NewFuncSlice(items ...Func) FuncSlice {
	slice := make(FuncSlice, len(items))
	for i, item := range items {
		slice[i] = item
	}
	return slice
}

func WithInitialFunc(t Func) FuncSliceReduceOption {
	return func(o *FuncSliceReduceOptions) {
		o.initial = t
	}
}

func WhereFuncAll(pl ...func(Func) bool) func(Func) bool {
	return func(t Func) bool {
		for _, p := range pl {
			if !p(t) {
				return false
			}
		}
		return true
	}
}

func WhereFuncAny(pl ...func(Func) bool) func(Func) bool {
	return func(t Func) bool {
		for _, p := range pl {
			if p(t) {
				return true
			}
		}
		return false
	}
}

func WhereFuncNot(p func(Func) bool) func(Func) bool {
	return func(t Func) bool {
		return !p(t)
	}
}

func (slice FuncSlice) Map(fn func(Func) Func) FuncSlice {
	mapped := make(FuncSlice, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice FuncSlice) AsyncMap(fn func(Func) Func, options ...FuncSliceAsyncOption) FuncSlice {
	output := make(FuncSlice, len(slice))
	eachFn := func(t Func, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.AsyncEachIndex(eachFn, options...)
	return output
}

func (slice FuncSlice) MapString(fn func(Func) string) []string {
	mapped := make([]string, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice FuncSlice) AsyncMapString(fn func(Func) string, options ...FuncSliceAsyncOption) []string {
	output := make([]string, len(slice))
	eachFn := func(t Func, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.AsyncEachIndex(eachFn, options...)
	return output
}

func (slice FuncSlice) MapBool(fn func(Func) bool) []bool {
	mapped := make([]bool, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice FuncSlice) AsyncMapBool(fn func(Func) bool, options ...FuncSliceAsyncOption) []bool {
	output := make([]bool, len(slice))
	eachFn := func(t Func, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.AsyncEachIndex(eachFn, options...)
	return output
}

func (slice FuncSlice) Filter(p func(Func) bool) FuncSlice {
	var selected FuncSlice
	for _, t := range slice {
		if p(t) {
			selected = append(selected, t)
		}
	}
	return selected
}

func (slice FuncSlice) IndexSelect(p func(Func) bool) []int {
	var indexes []int
	for i, t := range slice {
		if p(t) {
			indexes = append(indexes, i)
		}
	}
	return indexes
}

func (slice FuncSlice) SelectAsync(p func(Func) bool) FuncSlice {
	var selected FuncSlice
	hits := slice.AsyncMapBool(p)
	for i, t := range slice {
		if hits[i] {
			selected = append(selected, t)
		}
	}
	return selected
}

func (slice FuncSlice) Reject(p func(Func) bool) FuncSlice {
	return slice.Filter(func(t Func) bool { return !p(t) })
}

func (slice FuncSlice) Reduce(operator func(Func, Func) Func, options ...FuncSliceReduceOption) (result Func) {
	o := &FuncSliceReduceOptions{}
	for _, opt := range options {
		opt(o)
	}
	result = o.initial
	for _, next := range slice {
		result = operator(result, next)
	}
	return result
}

// If no predicate function parameters given returns true if slice is not empty.
// Otherwise, will return true if all predicate function parameters return true for any item in the slice
func (slice FuncSlice) Any(pl ...func(Func) bool) bool {
	if len(pl) == 0 {
		return len(slice) > 0
	}
	p := WhereFuncAll(pl...)
	for _, t := range slice {
		if p(t) {
			return true
		}
	}
	return false
}

func (slice FuncSlice) AnyNot(pl ...func(Func) bool) bool {
	return !slice.Any(pl...)
}

func (slice FuncSlice) All(p func(Func) bool) bool {
	for _, t := range slice {
		if !p(t) {
			return false
		}
	}
	return true
}

func (slice FuncSlice) AllNot(p func(Func) bool) bool {
	return !slice.All(p)
}

func (slice FuncSlice) Append(items ...Func) FuncSlice {
	if slice == nil {
		var empty FuncSlice
		return append(empty, items...)
	}
	return append(slice, items...)
}

func (slice FuncSlice) Count(p func(Func) bool) int {
	return len(slice.Filter(p))
}

func (slice FuncSlice) First(where ...func(Func) bool) Func {
	var r Func
	if len(slice) == 0 {
		return r
	}
	p := WhereFuncAll(where...)
	for _, t := range slice {
		if p(t) {
			r = t
			break
		}
	}
	return r
}

func (slice FuncSlice) FirstIndex(where ...func(Func) bool) int {
	if len(slice) == 0 {
		return -1
	}
	p := WhereFuncAll(where...)
	for i, t := range slice {
		if p(t) {
			return i
		}
	}
	return -1
}

func (slice FuncSlice) DistinctBy(match func(Func, Func) bool) (result FuncSlice) {
Outer:
	for _, v := range slice {
		for _, r := range result {
			if match(v, r) {
				continue Outer
			}
		}
		result = append(result, v)
	}
	return result
}

func (slice FuncSlice) Len() int {
	return len(slice)
}

func (slice FuncSlice) Each(f func(Func)) {
	for _, t := range slice {
		f(t)
	}
}

func (slice FuncSlice) AsyncEach(f func(Func)) {
	slice.AsyncEachIndex(func(t Func, _ int) {
		f(t)
	})
}

func newFuncSliceAsyncOptions(opts ...FuncSliceAsyncOption) *FuncSliceAsyncOptions {
	o := &FuncSliceAsyncOptions{PoolSize: runtime.NumCPU()}
	for _, opt := range opts {
		opt(o)
	}
	return o
}

func __FuncSliceEachIndexAsyncWorker(slice FuncSlice, f func(Func, int), pending <-chan int, completed chan<- int) {
	for index := range pending {
		item := slice[index]
		f(item, index)
		completed <- index
	}
}

func (slice FuncSlice) AsyncEachIndex(f func(Func, int), options ...FuncSliceAsyncOption) {
	o := newFuncSliceAsyncOptions(options...)
	pending := make(chan int, len(slice))
	completed := make(chan int, len(slice))
	for w := 0; w < o.PoolSize; w++ {
		go __FuncSliceEachIndexAsyncWorker(slice, f, pending, completed)
	}
	for index := range slice {
		pending <- index
	}
	close(pending)
	for _ = range slice {
		<-completed
	}
}

func (slice FuncSlice) EachIndex(f func(Func, int)) {
	for i, t := range slice {
		f(t, i)
	}
}

func (slice FuncSlice) Swap(i, j int) {
	slice[i], slice[j] = slice[j], slice[i]
}

func (slice FuncSlice) Empty() bool {
	return len(slice) == 0
}

func (slice FuncSlice) NotEmpty() bool {
	return len(slice) > 0
}

func (slice FuncSlice) Copy() FuncSlice {
	cp := make(FuncSlice, len(slice))
	for i := range slice {
		cp[i] = slice[i]
	}
	return cp
}

func (slice FuncSlice) Replace(fn func(t Func) Func) {
	for i, t := range slice {
		slice[i] = fn(t)
	}
}

func (slice FuncSlice) AsyncReplace(fn func(t Func) Func, options ...FuncSliceAsyncOption) {
	slice.AsyncEachIndex(func(t Func, i int) {
		slice[i] = fn(t)
	}, options...)
}

func (slice FuncSlice) Reversed() FuncSlice {
	r := slice.Copy()
	r.Reverse()
	return r
}

func (slice FuncSlice) Reverse() {
	for i, j := 0, len(slice)-1; i < j; i, j = i+1, j-1 {
		slice[i], slice[j] = slice[j], slice[i]
	}
}

func (slice FuncSlice) SortBy(less func(Func, Func) bool) {

	// Switch to heapsort if depth of 2*ceil(lg(n+1)) is reached.
	n := len(slice)
	maxDepth := 0
	for i := n; i > 0; i >>= 1 {
		maxDepth++
	}
	maxDepth *= 2
	quickSortFuncSlice(slice, less, 0, n, maxDepth)
}

func (slice FuncSlice) SortedBy(less func(Func, Func) bool) FuncSlice {
	cp := slice.Copy()
	cp.SortBy(less)
	return cp
}

func (slice FuncSlice) IsSortedBy(less func(Func, Func) bool) bool {
	n := len(slice)
	for i := n - 1; i > 0; i-- {
		if less(slice[i], slice[i-1]) {
			return false
		}
	}
	return true
}

func (slice FuncSlice) SortDescBy(less func(Func, Func) bool) {
	greater := func(a, b Func) bool {
		return less(b, a)
	}
	slice.SortBy(greater)
}

func (slice FuncSlice) SortedDescBy(less func(Func, Func) bool) FuncSlice {
	greater := func(a, b Func) bool {
		return less(b, a)
	}
	return slice.SortedBy(greater)
}

func (slice FuncSlice) IsSortedDescBy(less func(Func, Func) bool) bool {
	greater := func(a, b Func) bool {
		return less(b, a)
	}
	return slice.IsSortedBy(greater)
}

// Shuffled returns a copy of FuncSlice with the contents shuffles  using a version of the Fisher-Yates shuffle. See: http://clipperhouse.github.io/gen/#Shuffle
func (slice FuncSlice) Shuffled() FuncSlice {
	s := slice.Copy()
	s.Shuffle()
	return s
}

// Shuffle shuffles the contents of FuncSlice in place using a version of the Fisher-Yates shuffle. See: http://clipperhouse.github.io/gen/#Shuffle
func (slice FuncSlice) Shuffle() {
	total := len(slice)
	for i := 0; i < total; i++ {
		r := i + rand.Intn(total-i)
		slice[r], slice[i] = slice[i], slice[r]
	}
}

// MaxBy returns an element of FuncSlice containing the maximum value, when compared to other elements using a passed func defining ‘less’. In the case of multiple items being equally maximal, the last such element is returned. Returns error if no elements. See: http://clipperhouse.github.io/gen/#MaxBy
func (slice FuncSlice) MaxBy(less func(Func, Func) bool) (result Func, err error) {
	l := len(slice)
	if l == 0 {
		err = errors.New("cannot determine the MaxBy of an empty slice")
		return
	}
	m := 0
	for i := 1; i < l; i++ {
		if !less(slice[i], slice[m]) {
			m = i
		}
	}
	result = slice[m]
	return
}

// MinBy returns an element of FuncSlice containing the minimum value, when compared to other elements using a passed func defining ‘less’. In the case of multiple items being equally minimal, the first such element is returned. Returns error if no elements. See: http://clipperhouse.github.io/gen/#MinBy
func (slice FuncSlice) MinBy(less func(Func, Func) bool) (result Func, err error) {
	l := len(slice)
	if l == 0 {
		err = errors.New("cannot determine the Min of an empty slice")
		return
	}
	m := 0
	for i := 1; i < l; i++ {
		if less(slice[i], slice[m]) {
			m = i
		}
	}
	result = slice[m]
	return
}

func (slice FuncSlice) SkipTake(skip, take int) FuncSlice {
	var out FuncSlice
	skipped := 0
	taken := 0
	for _, item := range slice {
		if skip > skipped {
			skipped++
			continue
		}
		out = append(out, item)
		taken++
		if take > 0 && taken >= take {
			break
		}
	}
	return out

}
func swapFuncSlice(slice FuncSlice, a, b int) {
	slice[a], slice[b] = slice[b], slice[a]
}

// Insertion sort
func insertionSortFuncSlice(slice FuncSlice, less func(Func, Func) bool, a, b int) {
	for i := a + 1; i < b; i++ {
		for j := i; j > a && less(slice[j], slice[j-1]); j-- {
			swapFuncSlice(slice, j, j-1)
		}
	}
}

// siftDown implements the heap property on slice[lo, hi).
// first is an offset into the array where the root of the heap lies.
func siftDownFuncSlice(slice FuncSlice, less func(Func, Func) bool, lo, hi, first int) {
	root := lo
	for {
		child := 2*root + 1
		if child >= hi {
			break
		}
		if child+1 < hi && less(slice[first+child], slice[first+child+1]) {
			child++
		}
		if !less(slice[first+root], slice[first+child]) {
			return
		}
		swapFuncSlice(slice, first+root, first+child)
		root = child
	}
}
func heapSortFuncSlice(slice FuncSlice, less func(Func, Func) bool, a, b int) {
	first := a
	lo := 0
	hi := b - a
	// Build heap with greatest element at top.
	for i := (hi - 1) / 2; i >= 0; i-- {
		siftDownFuncSlice(slice, less, i, hi, first)
	}
	// Pop elements, largest first, into end of slice.
	for i := hi - 1; i >= 0; i-- {
		swapFuncSlice(slice, first, first+i)
		siftDownFuncSlice(slice, less, lo, i, first)
	}
}

// Quicksort, following Bentley and McIlroy,
// Engineering a Sort Function, SP&E November 1993.
// medianOfThree moves the median of the three values slice[a], slice[b], slice[c] into slice[a].
func medianOfThreeFuncSlice(slice FuncSlice, less func(Func, Func) bool, a, b, c int) {
	m0 := b
	m1 := a
	m2 := c
	// bubble sort on 3 elements
	if less(slice[m1], slice[m0]) {
		swapFuncSlice(slice, m1, m0)
	}
	if less(slice[m2], slice[m1]) {
		swapFuncSlice(slice, m2, m1)
	}
	if less(slice[m1], slice[m0]) {
		swapFuncSlice(slice, m1, m0)
	}
	// now slice[m0] <= slice[m1] <= slice[m2]
}
func swapRangeFuncSlice(slice FuncSlice, a, b, n int) {
	for i := 0; i < n; i++ {
		swapFuncSlice(slice, a+i, b+i)
	}
}
func doPivotFuncSlice(slice FuncSlice, less func(Func, Func) bool, lo, hi int) (midlo, midhi int) {
	m := lo + (hi-lo)/2 // Written like this to avoid integer overflow.
	if hi-lo > 40 {
		// Tukey's Ninther, median of three medians of three.
		s := (hi - lo) / 8
		medianOfThreeFuncSlice(slice, less, lo, lo+s, lo+2*s)
		medianOfThreeFuncSlice(slice, less, m, m-s, m+s)
		medianOfThreeFuncSlice(slice, less, hi-1, hi-1-s, hi-1-2*s)
	}
	medianOfThreeFuncSlice(slice, less, lo, m, hi-1)
	// Invariants are:
	//	slice[lo] = pivot (set up by ChoosePivot)
	//	slice[lo <= i < a] = pivot
	//	slice[a <= i < b] < pivot
	//	slice[b <= i < c] is unexamined
	//	slice[c <= i < d] > pivot
	//	slice[d <= i < hi] = pivot
	//
	// Once b meets c, can swap the "= pivot" sections
	// into the middle of the slice.
	pivot := lo
	a, b, c, d := lo+1, lo+1, hi, hi
	for {
		for b < c {
			if less(slice[b], slice[pivot]) { // slice[b] < pivot
				b++
			} else if !less(slice[pivot], slice[b]) { // slice[b] = pivot
				swapFuncSlice(slice, a, b)
				a++
				b++
			} else {
				break
			}
		}
		for b < c {
			if less(slice[pivot], slice[c-1]) { // slice[c-1] > pivot
				c--
			} else if !less(slice[c-1], slice[pivot]) { // slice[c-1] = pivot
				swapFuncSlice(slice, c-1, d-1)
				c--
				d--
			} else {
				break
			}
		}
		if b >= c {
			break
		}
		// slice[b] > pivot; slice[c-1] < pivot
		swapFuncSlice(slice, b, c-1)
		b++
		c--
	}
	min := func(a, b int) int {
		if a < b {
			return a
		}
		return b
	}
	n := min(b-a, a-lo)
	swapRangeFuncSlice(slice, lo, b-n, n)
	n = min(hi-d, d-c)
	swapRangeFuncSlice(slice, c, hi-n, n)
	return lo + b - a, hi - (d - c)
}

func (slice FuncSlice) Split(fn func(t Func) bool) (FuncSlice, FuncSlice) {
	var a FuncSlice
	var b FuncSlice
	for _, t := range slice {
		if fn(t) {
			a = append(a, t)
		} else {
			b = append(b, t)
		}
	}
	return a, b
}

func quickSortFuncSlice(slice FuncSlice, less func(Func, Func) bool, a, b, maxDepth int) {
	for b-a > 7 {
		if maxDepth == 0 {
			heapSortFuncSlice(slice, less, a, b)
			return
		}
		maxDepth--
		mlo, mhi := doPivotFuncSlice(slice, less, a, b)
		// Avoiding recursion on the larger subproblem guarantees
		// a stack depth of at most lg(b-a).
		if mlo-a < b-mhi {
			quickSortFuncSlice(slice, less, a, mlo, maxDepth)
			a = mhi // i.e., quickSortFuncSlice(slice, mhi, b)
		} else {
			quickSortFuncSlice(slice, less, mhi, b, maxDepth)
			b = mlo // i.e., quickSortFuncSlice(slice, a, mlo)
		}
	}
	if b-a > 1 {
		insertionSortFuncSlice(slice, less, a, b)
	}
}
