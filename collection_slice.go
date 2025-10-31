package collex

import (
	"errors"
	"math/rand"
	"runtime"
)

type CollectionSlice []Collection
type ColectionSliceReduceOption func(*reduceCollectionSliceOption)
type reduceCollectionSliceOption struct {
	initial Collection
}

func NewCollectionSlice(items ...Collection) CollectionSlice {
	slice := make(CollectionSlice, len(items))
	for i, item := range items {
		slice[i] = item
	}
	return slice
}

func WithInitialCollection(t Collection) ColectionSliceReduceOption {
	return func(o *reduceCollectionSliceOption) {
		o.initial = t
	}
}

func WhereCollectionAll(pl ...func(Collection) bool) func(Collection) bool {
	return func(t Collection) bool {
		for _, p := range pl {
			if !p(t) {
				return false
			}
		}
		return true
	}
}

func WhereCollectionAny(pl ...func(Collection) bool) func(Collection) bool {
	return func(t Collection) bool {
		for _, p := range pl {
			if p(t) {
				return true
			}
		}
		return false
	}
}

func WhereCollectionNot(p func(Collection) bool) func(Collection) bool {
	return func(t Collection) bool {
		return !p(t)
	}
}

func (slice CollectionSlice) Map(fn func(Collection) Collection) CollectionSlice {
	mapped := make(CollectionSlice, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice CollectionSlice) MapAsync(fn func(Collection) Collection, options ...CollectionSliceAsyncOption) CollectionSlice {
	output := make(CollectionSlice, len(slice))
	eachFn := func(t Collection, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.EachWithIndexAsync(eachFn, options...)
	return output
}

func (slice CollectionSlice) MapString(fn func(Collection) string) []string {
	mapped := make([]string, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice CollectionSlice) MapStringAsync(fn func(Collection) string, options ...CollectionSliceAsyncOption) []string {
	output := make([]string, len(slice))
	eachFn := func(t Collection, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.EachWithIndexAsync(eachFn, options...)
	return output
}

func (slice CollectionSlice) MapBool(fn func(Collection) bool) []bool {
	mapped := make([]bool, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice CollectionSlice) MapBoolAsync(fn func(Collection) bool, options ...CollectionSliceAsyncOption) []bool {
	output := make([]bool, len(slice))
	eachFn := func(t Collection, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.EachWithIndexAsync(eachFn, options...)
	return output
}

func (slice CollectionSlice) Filter(p func(Collection) bool) CollectionSlice {
	var selected CollectionSlice
	for _, t := range slice {
		if p(t) {
			selected = append(selected, t)
		}
	}
	return selected
}

func (slice CollectionSlice) SelectIndexes(p func(Collection) bool) []int {
	var indexes []int
	for i, t := range slice {
		if p(t) {
			indexes = append(indexes, i)
		}
	}
	return indexes
}

func (slice CollectionSlice) SelectAsync(p func(Collection) bool) CollectionSlice {
	var selected CollectionSlice
	hits := slice.MapBoolAsync(p)
	for i, t := range slice {
		if hits[i] {
			selected = append(selected, t)
		}
	}
	return selected
}

func (slice CollectionSlice) Reject(p func(Collection) bool) CollectionSlice {
	return slice.Filter(func(t Collection) bool { return !p(t) })
}

func (slice CollectionSlice) Reduce(operator func(Collection, Collection) Collection, options ...ColectionSliceReduceOption) (result Collection) {
	o := &reduceCollectionSliceOption{}
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
func (slice CollectionSlice) Any(pl ...func(Collection) bool) bool {
	if len(pl) == 0 {
		return len(slice) > 0
	}
	p := WhereCollectionAll(pl...)
	for _, t := range slice {
		if p(t) {
			return true
		}
	}
	return false
}

func (slice CollectionSlice) NotAny(pl ...func(Collection) bool) bool {
	return !slice.Any(pl...)
}

func (slice CollectionSlice) All(p func(Collection) bool) bool {
	for _, t := range slice {
		if !p(t) {
			return false
		}
	}
	return true
}

func (slice CollectionSlice) NotAll(p func(Collection) bool) bool {
	return !slice.All(p)
}

func (slice CollectionSlice) Append(items ...Collection) CollectionSlice {
	if slice == nil {
		var empty CollectionSlice
		return append(empty, items...)
	}
	return append(slice, items...)
}

func (slice CollectionSlice) Count(p func(Collection) bool) int {
	return len(slice.Filter(p))
}

func (slice CollectionSlice) First(where ...func(Collection) bool) Collection {
	var r Collection
	if len(slice) == 0 {
		return r
	}
	p := WhereCollectionAll(where...)
	for _, t := range slice {
		if p(t) {
			r = t
			break
		}
	}
	return r
}

func (slice CollectionSlice) FirstIndex(where ...func(Collection) bool) int {
	if len(slice) == 0 {
		return -1
	}
	p := WhereCollectionAll(where...)
	for i, t := range slice {
		if p(t) {
			return i
		}
	}
	return -1
}

func (slice CollectionSlice) DistinctBy(match func(Collection, Collection) bool) (result CollectionSlice) {
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

func (slice CollectionSlice) Len() int {
	return len(slice)
}

func (slice CollectionSlice) Each(f func(Collection)) {
	for _, t := range slice {
		f(t)
	}
}

func (slice CollectionSlice) EachAsync(f func(Collection)) {
	slice.EachWithIndexAsync(func(t Collection, _ int) {
		f(t)
	})
}

type CollectionSliceAsyncOption func(options *_CollectionSliceAsyncOptions)
type _CollectionSliceAsyncOptions struct {
	PoolSize int
}

func WithCollectionAsyncPoolSize(size int) CollectionSliceAsyncOption {
	return func(options *_CollectionSliceAsyncOptions) {
		options.PoolSize = size
	}
}

func newCollectionSliceAsyncOptions(opts ...CollectionSliceAsyncOption) *_CollectionSliceAsyncOptions {
	o := &_CollectionSliceAsyncOptions{PoolSize: runtime.NumCPU()}
	for _, opt := range opts {
		opt(o)
	}
	return o
}

func __CollectionSliceEachIndexAsyncWorker(slice CollectionSlice, f func(Collection, int), pending <-chan int, completed chan<- int) {
	for index := range pending {
		item := slice[index]
		f(item, index)
		completed <- index
	}
}

func (slice CollectionSlice) EachWithIndexAsync(f func(Collection, int), options ...CollectionSliceAsyncOption) {
	o := newCollectionSliceAsyncOptions(options...)
	pending := make(chan int, len(slice))
	completed := make(chan int, len(slice))
	for w := 0; w < o.PoolSize; w++ {
		go __CollectionSliceEachIndexAsyncWorker(slice, f, pending, completed)
	}
	for index := range slice {
		pending <- index
	}
	close(pending)
	for _ = range slice {
		<-completed
	}
}

func (slice CollectionSlice) EachWithIndex(f func(Collection, int)) {
	for i, t := range slice {
		f(t, i)
	}
}

func (slice CollectionSlice) Swap(i, j int) {
	slice[i], slice[j] = slice[j], slice[i]
}

func (slice CollectionSlice) Empty() bool {
	return len(slice) == 0
}

func (slice CollectionSlice) NotEmpty() bool {
	return len(slice) > 0
}

func (slice CollectionSlice) Copy() CollectionSlice {
	cp := make(CollectionSlice, len(slice))
	for i := range slice {
		cp[i] = slice[i]
	}
	return cp
}

func (slice CollectionSlice) ReplaceEach(fn func(t Collection) Collection) {
	for i, t := range slice {
		slice[i] = fn(t)
	}
}

func (slice CollectionSlice) ReplaceEachAsync(fn func(t Collection) Collection, options ...CollectionSliceAsyncOption) {
	slice.EachWithIndexAsync(func(t Collection, i int) {
		slice[i] = fn(t)
	}, options...)
}

func (slice CollectionSlice) SortBy(less func(Collection, Collection) bool) {

	// Switch to heapsort if depth of 2*ceil(lg(n+1)) is reached.
	n := len(slice)
	maxDepth := 0
	for i := n; i > 0; i >>= 1 {
		maxDepth++
	}
	maxDepth *= 2
	quickSortCollectionSlice(slice, less, 0, n, maxDepth)
}

func (slice CollectionSlice) SortedBy(less func(Collection, Collection) bool) CollectionSlice {
	cp := slice.Copy()
	cp.SortBy(less)
	return cp
}

func (slice CollectionSlice) IsSortedBy(less func(Collection, Collection) bool) bool {
	n := len(slice)
	for i := n - 1; i > 0; i-- {
		if less(slice[i], slice[i-1]) {
			return false
		}
	}
	return true
}

func (slice CollectionSlice) SortDescBy(less func(Collection, Collection) bool) {
	greater := func(a, b Collection) bool {
		return less(b, a)
	}
	slice.SortBy(greater)
}

func (slice CollectionSlice) SortedDescBy(less func(Collection, Collection) bool) CollectionSlice {
	greater := func(a, b Collection) bool {
		return less(b, a)
	}
	return slice.SortedBy(greater)
}

func (slice CollectionSlice) IsSortedDescBy(less func(Collection, Collection) bool) bool {
	greater := func(a, b Collection) bool {
		return less(b, a)
	}
	return slice.IsSortedBy(greater)
}

// Shuffled returns a copy of CollectionSlice with the contents shuffles  using a version of the Fisher-Yates shuffle. See: http://clipperhouse.github.io/gen/#Shuffle
func (slice CollectionSlice) Shuffled() CollectionSlice {
	s := slice.Copy()
	s.Shuffle()
	return s
}

// Shuffle shuffles the contents of CollectionSlice in place using a version of the Fisher-Yates shuffle. See: http://clipperhouse.github.io/gen/#Shuffle
func (slice CollectionSlice) Shuffle() {
	total := len(slice)
	for i := 0; i < total; i++ {
		r := i + rand.Intn(total-i)
		slice[r], slice[i] = slice[i], slice[r]
	}
}

// MaxBy returns an element of CollectionSlice containing the maximum value, when compared to other elements using a passed func defining ‘less’. In the case of multiple items being equally maximal, the last such element is returned. Returns error if no elements. See: http://clipperhouse.github.io/gen/#MaxBy
func (slice CollectionSlice) MaxBy(less func(Collection, Collection) bool) (result Collection, err error) {
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

// MinBy returns an element of CollectionSlice containing the minimum value, when compared to other elements using a passed func defining ‘less’. In the case of multiple items being equally minimal, the first such element is returned. Returns error if no elements. See: http://clipperhouse.github.io/gen/#MinBy
func (slice CollectionSlice) MinBy(less func(Collection, Collection) bool) (result Collection, err error) {
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

func (slice CollectionSlice) SkipTake(skip, take int) CollectionSlice {
	var out CollectionSlice
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
func swapCollectionSlice(slice CollectionSlice, a, b int) {
	slice[a], slice[b] = slice[b], slice[a]
}

// Insertion sort
func insertionSortCollectionSlice(slice CollectionSlice, less func(Collection, Collection) bool, a, b int) {
	for i := a + 1; i < b; i++ {
		for j := i; j > a && less(slice[j], slice[j-1]); j-- {
			swapCollectionSlice(slice, j, j-1)
		}
	}
}

// siftDown implements the heap property on slice[lo, hi).
// first is an offset into the array where the root of the heap lies.
func siftDownCollectionSlice(slice CollectionSlice, less func(Collection, Collection) bool, lo, hi, first int) {
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
		swapCollectionSlice(slice, first+root, first+child)
		root = child
	}
}
func heapSortCollectionSlice(slice CollectionSlice, less func(Collection, Collection) bool, a, b int) {
	first := a
	lo := 0
	hi := b - a
	// Build heap with greatest element at top.
	for i := (hi - 1) / 2; i >= 0; i-- {
		siftDownCollectionSlice(slice, less, i, hi, first)
	}
	// Pop elements, largest first, into end of slice.
	for i := hi - 1; i >= 0; i-- {
		swapCollectionSlice(slice, first, first+i)
		siftDownCollectionSlice(slice, less, lo, i, first)
	}
}

// Quicksort, following Bentley and McIlroy,
// Engineering a Sort Collectiontion, SP&E November 1993.
// medianOfThree moves the median of the three values slice[a], slice[b], slice[c] into slice[a].
func medianOfThreeCollectionSlice(slice CollectionSlice, less func(Collection, Collection) bool, a, b, c int) {
	m0 := b
	m1 := a
	m2 := c
	// bubble sort on 3 elements
	if less(slice[m1], slice[m0]) {
		swapCollectionSlice(slice, m1, m0)
	}
	if less(slice[m2], slice[m1]) {
		swapCollectionSlice(slice, m2, m1)
	}
	if less(slice[m1], slice[m0]) {
		swapCollectionSlice(slice, m1, m0)
	}
	// now slice[m0] <= slice[m1] <= slice[m2]
}
func swapRangeCollectionSlice(slice CollectionSlice, a, b, n int) {
	for i := 0; i < n; i++ {
		swapCollectionSlice(slice, a+i, b+i)
	}
}
func doPivotCollectionSlice(slice CollectionSlice, less func(Collection, Collection) bool, lo, hi int) (midlo, midhi int) {
	m := lo + (hi-lo)/2 // Written like this to avoid integer overflow.
	if hi-lo > 40 {
		// Tukey's Ninther, median of three medians of three.
		s := (hi - lo) / 8
		medianOfThreeCollectionSlice(slice, less, lo, lo+s, lo+2*s)
		medianOfThreeCollectionSlice(slice, less, m, m-s, m+s)
		medianOfThreeCollectionSlice(slice, less, hi-1, hi-1-s, hi-1-2*s)
	}
	medianOfThreeCollectionSlice(slice, less, lo, m, hi-1)
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
				swapCollectionSlice(slice, a, b)
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
				swapCollectionSlice(slice, c-1, d-1)
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
		swapCollectionSlice(slice, b, c-1)
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
	swapRangeCollectionSlice(slice, lo, b-n, n)
	n = min(hi-d, d-c)
	swapRangeCollectionSlice(slice, c, hi-n, n)
	return lo + b - a, hi - (d - c)
}

func (slice CollectionSlice) Split(fn func(t Collection) bool) (CollectionSlice, CollectionSlice) {
	var a CollectionSlice
	var b CollectionSlice
	for _, t := range slice {
		if fn(t) {
			a = append(a, t)
		} else {
			b = append(b, t)
		}
	}
	return a, b
}

func quickSortCollectionSlice(slice CollectionSlice, less func(Collection, Collection) bool, a, b, maxDepth int) {
	for b-a > 7 {
		if maxDepth == 0 {
			heapSortCollectionSlice(slice, less, a, b)
			return
		}
		maxDepth--
		mlo, mhi := doPivotCollectionSlice(slice, less, a, b)
		// Avoiding recursion on the larger subproblem guarantees
		// a stack depth of at most lg(b-a).
		if mlo-a < b-mhi {
			quickSortCollectionSlice(slice, less, a, mlo, maxDepth)
			a = mhi // i.e., quickSortCollectionSlice(slice, mhi, b)
		} else {
			quickSortCollectionSlice(slice, less, mhi, b, maxDepth)
			b = mlo // i.e., quickSortCollectionSlice(slice, a, mlo)
		}
	}
	if b-a > 1 {
		insertionSortCollectionSlice(slice, less, a, b)
	}
}

func (slice CollectionSlice) Flatten() Collection {
	return slice.Reduce(func(s1, s2 Collection) Collection {
		return append(s1, s2...)
	})
}
