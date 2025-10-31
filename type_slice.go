package collex

import (
	"errors"
	"fmt"
	"math/rand"
	"strings"
	"sync"
)

type TypeSlice []Type
type TypeSliceReduceOption func(*TypeSliceReduceOptions)
type TypeSliceReduceOptions struct {
	initial Type
}

type TypeSliceAsyncOption func(options *TypeSliceAsyncOptions)
type TypeSliceAsyncOptions struct {
	PoolSize int
}

func NewTypeSlice(items ...Type) TypeSlice {
	slice := make(TypeSlice, len(items))
	for i, item := range items {
		slice[i] = item
	}
	return slice
}

func WithInitialType(t Type) TypeSliceReduceOption {
	return func(o *TypeSliceReduceOptions) {
		o.initial = t
	}
}

func WhereTypeAll(pl ...func(Type) bool) func(Type) bool {
	return func(t Type) bool {
		for _, p := range pl {
			if !p(t) {
				return false
			}
		}
		return true
	}
}

func WhereTypeAny(pl ...func(Type) bool) func(Type) bool {
	return func(t Type) bool {
		for _, p := range pl {
			if p(t) {
				return true
			}
		}
		return false
	}
}

func WhereTypeNot(p func(Type) bool) func(Type) bool {
	return func(t Type) bool {
		return !p(t)
	}
}

func (slice TypeSlice) Index(item Type) int {
	for i, t := range slice {
		if item == t {
			return i
		}
	}
	return -1
}

// Returns copy of slice with only items that have non-default values
// (e.g. for pointer types all non-nil items)
func (slice TypeSlice) Compact() TypeSlice {
	var dfl Type
	s := NewTypeSlice()
	for _, t := range slice {
		if t == dfl {
			continue
		}
		s = append(s, t)
	}
	return s
}

func (slice TypeSlice) Map(fn func(Type) Type) TypeSlice {
	mapped := make(TypeSlice, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice TypeSlice) AsyncMap(fn func(Type) Type, options ...TypeSliceAsyncOption) TypeSlice {
	output := make(TypeSlice, len(slice))
	eachFn := func(t Type, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.AsyncEachIndex(eachFn, options...)
	return output
}

func (slice TypeSlice) MapString(fn func(Type) string) []string {
	mapped := make([]string, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice TypeSlice) AsyncMapString(fn func(Type) string, options ...TypeSliceAsyncOption) []string {
	output := make([]string, len(slice))
	eachFn := func(t Type, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.AsyncEachIndex(eachFn, options...)
	return output
}

func (slice TypeSlice) MapBool(fn func(Type) bool) []bool {
	mapped := make([]bool, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice TypeSlice) AsyncMapBool(fn func(Type) bool, options ...TypeSliceAsyncOption) []bool {
	output := make([]bool, len(slice))
	eachFn := func(t Type, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.AsyncEachIndex(eachFn, options...)
	return output
}

func (slice TypeSlice) Filter(where func(Type) bool, ands ...func(Type) bool) TypeSlice {
	if len(ands) > 0 {
		where = WhereTypeAll(append([]func(Type) bool{where}, ands...)...)
	}
	var selected TypeSlice
	for _, t := range slice {
		if where(t) {
			selected = append(selected, t)
		}
	}
	return selected
}

func (slice TypeSlice) Reversed() TypeSlice {
	s2 := make(TypeSlice, len(slice))
	for i, j := 0, len(slice)-1; i < j; i, j = i+1, j-1 {
		s2[i] = slice[j]
	}
	r := slice.Copy()
	r.Reverse()
	return r
}

func (slice TypeSlice) Reverse() {
	for i, j := 0, len(slice)-1; i < j; i, j = i+1, j-1 {
		slice[i], slice[j] = slice[j], slice[i]
	}
}

func (slice TypeSlice) ReverseSelect(where func(Type) bool, ands ...func(Type) bool) TypeSlice {
	if len(ands) > 0 {
		where = WhereTypeAll(append([]func(Type) bool{where}, ands...)...)
	}
	var selected TypeSlice
	for i := len(slice) - 1; i >= 0; i-- {
		t := slice[i]
		if where(t) {
			selected = append(selected, t)
		}
	}
	return selected
}

func (slice TypeSlice) IndexSelect(p func(Type) bool) []int {
	var indexes []int
	for i, t := range slice {
		if p(t) {
			indexes = append(indexes, i)
		}
	}
	return indexes
}

// safe index access -- allows negative indexing, and will error instead of panic if out of bounds
func (slice TypeSlice) Item(index int) (item Type, err error) {
	if index < 0 {
		index = len(slice) - index
	}
	if index < 0 || index > len(slice)+1 {
		err = fmt.Errorf("index out of range")
	} else {
		item = slice[index]
	}
	return item, err
}

func (slice TypeSlice) SelectAsync(p func(Type) bool) TypeSlice {
	var selected TypeSlice
	hits := slice.AsyncMapBool(p)
	for i, t := range slice {
		if hits[i] {
			selected = append(selected, t)
		}
	}
	return selected
}

func (slice TypeSlice) Reject(p func(Type) bool) TypeSlice {
	return slice.Filter(func(t Type) bool { return !p(t) })
}

func (slice TypeSlice) Reduce(operator func(Type, Type) Type, options ...TypeSliceReduceOption) (result Type) {
	o := &TypeSliceReduceOptions{}
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
// Otherwise, will walk the slice backwards and return true for the first item where all the predicates
// return true
func (slice TypeSlice) ReverseAny(criteria ...func(Type) bool) bool {
	if len(criteria) == 0 {
		return len(slice) > 0
	}
	p := WhereTypeAll(criteria...)
	for i := len(slice) - 1; i >= 0; i-- {
		t := slice[i]
		if p(t) {
			return true
		}
	}
	return false
}

// If no predicate function parameters given returns true if slice is not empty.
// Otherwise, will return true if all predicate function parameters return true for any item in the slice
func (slice TypeSlice) Any(pl ...func(Type) bool) bool {
	if len(pl) == 0 {
		return len(slice) > 0
	}
	p := WhereTypeAll(pl...)
	for _, t := range slice {
		if p(t) {
			return true
		}
	}
	return false
}

func (slice TypeSlice) ContainsAll(items ...Type) bool {
	for _, item := range items {
		itemMatch := false
		for _, t := range slice {
			if item == t {
				itemMatch = true
				break
			}
		}
		if !itemMatch {
			return false
		}
	}
	return true
}

func (slice TypeSlice) ContainsAny(items ...Type) bool {
	for _, t := range slice {
		for _, item := range items {
			if item == t {
				return true
			}
		}
	}
	return false
}

func (slice TypeSlice) PopLast() (last Type, rest TypeSlice) {
	l := len(slice)
	if l > 0 {
		last = slice[len(slice)-1]
	}
	if l > 1 {
		rest = slice[0 : len(slice)-1]
	}
	return last, rest
}

func (slice TypeSlice) PopFirst() (first Type, rest TypeSlice) {
	l := len(slice)
	if l > 0 {
		first = slice[0]
	}
	if l > 1 {
		rest = slice[1:]
	}
	return first, rest
}

func (slice TypeSlice) String() string {
	if slice == nil {
		return fmt.Sprint(nil)
	}
	return fmt.Sprintf("[%v]", strings.Join(slice.Strings(), ", "))
}

func (slice TypeSlice) Strings() []string {
	return slice.MapString(func(x Type) string {
		return fmt.Sprintf("%v", x)
	})
}
func (slice TypeSlice) Pop(index int) (popped Type, rest TypeSlice) {
	if index < 0 {
		index = len(slice) - index
	}
	if index <= 0 {
		return slice.PopFirst()
	}
	if index >= len(slice)-1 {
		return slice.PopLast()
	}
	for i, item := range slice {
		if i == index {
			popped = item
		} else {
			rest = append(rest, item)
		}
	}
	return popped, rest
}

func (slice TypeSlice) Contains(item Type) bool {
	for _, t := range slice {
		if item == t {
			return true
		}
	}
	return false
}

func (slice TypeSlice) AnyNot(pl ...func(Type) bool) bool {
	return !slice.Any(pl...)
}

func (slice TypeSlice) All(p func(Type) bool) bool {
	for _, t := range slice {
		if !p(t) {
			return false
		}
	}
	return true
}

func (slice TypeSlice) AllNot(p func(Type) bool) bool {
	return !slice.All(p)
}

func (slice TypeSlice) Append(items ...Type) TypeSlice {
	if slice == nil {
		var empty TypeSlice
		return append(empty, items...)
	}
	return append(slice, items...)
}

func (slice TypeSlice) Count(p func(Type) bool) int {
	return len(slice.Filter(p))
}

func (slice TypeSlice) Equal(other []Type) bool {
	if len(slice) != len(other) {
		return false
	}
	for n := range slice {
		if slice[n] != other[n] {
			return false
		}
	}
	return true
}

func (slice TypeSlice) Last(where ...func(Type) bool) (last Type) {
	hasCriteria := len(where) > 0
	matchesCriteria := WhereTypeAll(where...)
	for i := len(slice) - 1; i >= 0; i-- {
		t := slice[i]
		if !hasCriteria || matchesCriteria(t) {
			last = t
			break
		}
	}
	return last
}

func (slice TypeSlice) First(where ...func(Type) bool) (first Type) {
	hasCriteria := len(where) > 0
	matchesCriteria := WhereTypeAll(where...)
	for _, t := range slice {
		if !hasCriteria || matchesCriteria(t) {
			first = t
			break
		}
	}
	return first
}

func (slice TypeSlice) FirstIndex(where ...func(Type) bool) int {
	if len(slice) == 0 {
		return -1
	}
	p := WhereTypeAll(where...)
	for i, t := range slice {
		if p(t) {
			return i
		}
	}
	return -1
}

func (slice TypeSlice) DistinctBy(match func(Type, Type) bool) (result TypeSlice) {
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

func (slice TypeSlice) Len() int {
	return len(slice)
}

func (slice TypeSlice) Each(f func(Type)) {
	for _, t := range slice {
		f(t)
	}
}

func (slice TypeSlice) AsyncEach(f func(Type), options ...TypeSliceAsyncOption) {
	slice.AsyncEachIndex(func(t Type, _ int) {
		f(t)
	}, options...)
}

func WithTypeAsyncPoolSize(size int) TypeSliceAsyncOption {
	return func(options *TypeSliceAsyncOptions) {
		options.PoolSize = size
	}
}

func newTypeSliceAsyncOptions(opts ...TypeSliceAsyncOption) *TypeSliceAsyncOptions {
	o := &TypeSliceAsyncOptions{PoolSize: -1}
	for _, opt := range opts {
		opt(o)
	}
	return o
}

func (slice TypeSlice) AsyncEachIndex(f func(Type, int), options ...TypeSliceAsyncOption) {
	o := newTypeSliceAsyncOptions(options...)
	if o.PoolSize <= 0 {
		wg := &sync.WaitGroup{}
		for index, item := range slice {
			wg.Add(1)
			go func(item Type, index int) {
				f(item, index)
				wg.Done()
			}(item, index)
		}
		wg.Wait()
		return
	}
	pending := make(chan int, len(slice))
	completed := make(chan int, len(slice))
	for w := 0; w < o.PoolSize; w++ {
		go func(slice TypeSlice, f func(Type, int), pending <-chan int, completed chan<- int) {
			for index := range pending {
				item := slice[index]
				f(item, index)
				completed <- index
			}
		}(slice, f, pending, completed)
	}
	for index := range slice {
		pending <- index
	}
	close(pending)
	for range slice {
		<-completed
	}
}

func (slice TypeSlice) EachIndex(f func(Type, int)) {
	for i, t := range slice {
		f(t, i)
	}
}

func (slice TypeSlice) Swap(i, j int) {
	slice[i], slice[j] = slice[j], slice[i]
}

func (slice TypeSlice) Empty() bool {
	return len(slice) == 0
}

func (slice TypeSlice) NotEmpty() bool {
	return len(slice) > 0
}

func (slice TypeSlice) AsyncCopy() TypeSlice {
	cp := make(TypeSlice, len(slice))
	slice.AsyncEachIndex(func(_ Type, i int) {
		cp[i] = slice[i]
	})
	return cp
}

func (slice TypeSlice) Copy() TypeSlice {
	cp := make(TypeSlice, len(slice))
	for i := range slice {
		cp[i] = slice[i]
	}
	return cp
}

func (slice TypeSlice) SortBy(less func(Type, Type) bool) {

	// Switch to heapsort if depth of 2*ceil(lg(n+1)) is reached.
	n := len(slice)
	maxDepth := 0
	for i := n; i > 0; i >>= 1 {
		maxDepth++
	}
	maxDepth *= 2
	__quickSortTypeSlice(slice, less, 0, n, maxDepth)
}

func (slice TypeSlice) SortedBy(less func(Type, Type) bool) TypeSlice {
	cp := slice.Copy()
	cp.SortBy(less)
	return cp
}

func (slice TypeSlice) IsSortedBy(less func(Type, Type) bool) bool {
	n := len(slice)
	for i := n - 1; i > 0; i-- {
		if less(slice[i], slice[i-1]) {
			return false
		}
	}
	return true
}

func (slice TypeSlice) SortDescBy(less func(Type, Type) bool) {
	greater := func(a, b Type) bool {
		return less(b, a)
	}
	slice.SortBy(greater)
}

func (slice TypeSlice) SortedDescBy(less func(Type, Type) bool) TypeSlice {
	greater := func(a, b Type) bool {
		return less(b, a)
	}
	return slice.SortedBy(greater)
}

func (slice TypeSlice) IsSortedDescBy(less func(Type, Type) bool) bool {
	greater := func(a, b Type) bool {
		return less(b, a)
	}
	return slice.IsSortedBy(greater)
}

// Shuffled returns a copy of TypeSlice with the contents shuffles  using a version of the Fisher-Yates shuffle. See: http://clipperhouse.github.io/gen/#Shuffle
func (slice TypeSlice) Shuffled() TypeSlice {
	s := slice.Copy()
	s.Shuffle()
	return s
}

// Shuffle shuffles the contents of TypeSlice in place using a version of the Fisher-Yates shuffle. See: http://clipperhouse.github.io/gen/#Shuffle
func (slice TypeSlice) Shuffle() {
	total := len(slice)
	for i := 0; i < total; i++ {
		r := i + rand.Intn(total-i)
		slice[r], slice[i] = slice[i], slice[r]
	}
}

// MaxBy returns an element of TypeSlice containing the maximum value, when compared to other elements using a passed func defining ‘less’. In the case of multiple items being equally maximal, the last such element is returned. Returns error if no elements. See: http://clipperhouse.github.io/gen/#MaxBy
func (slice TypeSlice) MaxBy(less func(Type, Type) bool) (result Type, err error) {
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

// MinBy returns an element of TypeSlice containing the minimum value, when compared to other elements using a passed func defining ‘less’. In the case of multiple items being equally minimal, the first such element is returned. Returns error if no elements. See: http://clipperhouse.github.io/gen/#MinBy
func (slice TypeSlice) MinBy(less func(Type, Type) bool) (result Type, err error) {
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

func (slice TypeSlice) AsyncReplaced(fn func(t Type) Type) TypeSlice {
	s := slice.Copy()
	s.AsyncReplace(fn)
	return s
}

func (slice TypeSlice) Replaced(fn func(t Type) Type) TypeSlice {
	s := slice.Copy()
	s.Replace(fn)
	return s
}

func (slice TypeSlice) Replace(fn func(t Type) Type) {
	for i, t := range slice {
		slice[i] = fn(t)
	}
}

func (slice TypeSlice) AsyncReplace(fn func(t Type) Type, options ...TypeSliceAsyncOption) {
	slice.AsyncEachIndex(func(t Type, i int) {
		slice[i] = fn(t)
	}, options...)
}

func (slice TypeSlice) SkipTake(skip, take int) TypeSlice {
	var out TypeSlice
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
func (slice TypeSlice) Split(fn func(t Type) bool) (TypeSlice, TypeSlice) {
	var a TypeSlice
	var b TypeSlice
	for _, t := range slice {
		if fn(t) {
			a = append(a, t)
		} else {
			b = append(b, t)
		}
	}
	return a, b
}

func __swapTypeSlice(slice TypeSlice, a, b int) {
	slice[a], slice[b] = slice[b], slice[a]
}

// Insertion sort
func __insertionSortTypeSlice(slice TypeSlice, less func(Type, Type) bool, a, b int) {
	for i := a + 1; i < b; i++ {
		for j := i; j > a && less(slice[j], slice[j-1]); j-- {
			__swapTypeSlice(slice, j, j-1)
		}
	}
}

// siftDown implements the heap property on slice[lo, hi).
// first is an offset into the array where the root of the heap lies.
func __siftDownTypeSlice(slice TypeSlice, less func(Type, Type) bool, lo, hi, first int) {
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
		__swapTypeSlice(slice, first+root, first+child)
		root = child
	}
}
func __heapSortTypeSlice(slice TypeSlice, less func(Type, Type) bool, a, b int) {
	first := a
	lo := 0
	hi := b - a
	// Build heap with greatest element at top.
	for i := (hi - 1) / 2; i >= 0; i-- {
		__siftDownTypeSlice(slice, less, i, hi, first)
	}
	// Pop elements, largest first, into end of slice.
	for i := hi - 1; i >= 0; i-- {
		__swapTypeSlice(slice, first, first+i)
		__siftDownTypeSlice(slice, less, lo, i, first)
	}
}

// Quicksort, following Bentley and McIlroy,
// Engineering a Sort Function, SP&E November 1993.
// medianOfThree moves the median of the three values slice[a], slice[b], slice[c] into slice[a].
func __medianOfThreeTypeSlice(slice TypeSlice, less func(Type, Type) bool, a, b, c int) {
	m0 := b
	m1 := a
	m2 := c
	// bubble sort on 3 elements
	if less(slice[m1], slice[m0]) {
		__swapTypeSlice(slice, m1, m0)
	}
	if less(slice[m2], slice[m1]) {
		__swapTypeSlice(slice, m2, m1)
	}
	if less(slice[m1], slice[m0]) {
		__swapTypeSlice(slice, m1, m0)
	}
	// now slice[m0] <= slice[m1] <= slice[m2]
}

func __swapRangeTypeSlice(slice TypeSlice, a, b, n int) {
	for i := 0; i < n; i++ {
		__swapTypeSlice(slice, a+i, b+i)
	}
}
func __doPivotTypeSlice(slice TypeSlice, less func(Type, Type) bool, lo, hi int) (midlo, midhi int) {
	m := lo + (hi-lo)/2 // Written like this to avoid integer overflow.
	if hi-lo > 40 {
		// Tukey's Ninther, median of three medians of three.
		s := (hi - lo) / 8
		__medianOfThreeTypeSlice(slice, less, lo, lo+s, lo+2*s)
		__medianOfThreeTypeSlice(slice, less, m, m-s, m+s)
		__medianOfThreeTypeSlice(slice, less, hi-1, hi-1-s, hi-1-2*s)
	}
	__medianOfThreeTypeSlice(slice, less, lo, m, hi-1)
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
				__swapTypeSlice(slice, a, b)
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
				__swapTypeSlice(slice, c-1, d-1)
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
		__swapTypeSlice(slice, b, c-1)
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
	__swapRangeTypeSlice(slice, lo, b-n, n)
	n = min(hi-d, d-c)
	__swapRangeTypeSlice(slice, c, hi-n, n)
	return lo + b - a, hi - (d - c)
}

func __quickSortTypeSlice(slice TypeSlice, less func(Type, Type) bool, a, b, maxDepth int) {
	for b-a > 7 {
		if maxDepth == 0 {
			__heapSortTypeSlice(slice, less, a, b)
			return
		}
		maxDepth--
		mlo, mhi := __doPivotTypeSlice(slice, less, a, b)
		// Avoiding recursion on the larger subproblem guarantees
		// a stack depth of at most lg(b-a).
		if mlo-a < b-mhi {
			__quickSortTypeSlice(slice, less, a, mlo, maxDepth)
			a = mhi // i.e., quickSortTypeSlice(slice, mhi, b)
		} else {
			__quickSortTypeSlice(slice, less, mhi, b, maxDepth)
			b = mlo // i.e., quickSortTypeSlice(slice, a, mlo)
		}
	}
	if b-a > 1 {
		__insertionSortTypeSlice(slice, less, a, b)
	}
}
