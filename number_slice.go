package collex

import (
	"errors"
	"fmt"
	"math/rand"
	"sort"
	"strings"
	"sync"
)

type NumberSlice []Number
type NumberSliceReduceOption func(*NumberSliceReduceOptions)
type NumberSliceReduceOptions struct {
	initial Number
}

type NumberSliceAsyncOption func(options *NumberSliceAsyncOptions)
type NumberSliceAsyncOptions struct {
	PoolSize int
}

func NewNumberSlice(items ...Number) NumberSlice {
	slice := make(NumberSlice, len(items))
	for i, item := range items {
		slice[i] = item
	}
	return slice
}

func WithInitialNumber(t Number) NumberSliceReduceOption {
	return func(o *NumberSliceReduceOptions) {
		o.initial = t
	}
}

func WhereNumberAll(pl ...func(Number) bool) func(Number) bool {
	return func(t Number) bool {
		for _, p := range pl {
			if !p(t) {
				return false
			}
		}
		return true
	}
}

func WhereNumberAny(pl ...func(Number) bool) func(Number) bool {
	return func(t Number) bool {
		for _, p := range pl {
			if p(t) {
				return true
			}
		}
		return false
	}
}

func WhereNumberNot(p func(Number) bool) func(Number) bool {
	return func(t Number) bool {
		return !p(t)
	}
}

func (slice NumberSlice) Index(item Number) int {
	for i, t := range slice {
		if item == t {
			return i
		}
	}
	return -1
}

func (slice NumberSlice) Map(fn func(Number) Number) NumberSlice {
	mapped := make(NumberSlice, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice NumberSlice) AsyncMap(fn func(Number) Number, options ...NumberSliceAsyncOption) NumberSlice {
	output := make(NumberSlice, len(slice))
	eachFn := func(t Number, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.AsyncEachIndex(eachFn, options...)
	return output
}

func (slice NumberSlice) MapString(fn func(Number) string) []string {
	mapped := make([]string, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice NumberSlice) AsyncMapString(fn func(Number) string, options ...NumberSliceAsyncOption) []string {
	output := make([]string, len(slice))
	eachFn := func(t Number, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.AsyncEachIndex(eachFn, options...)
	return output
}

func (slice NumberSlice) MapBool(fn func(Number) bool) []bool {
	mapped := make([]bool, len(slice))
	for i, t := range slice {
		mapped[i] = fn(t)
	}
	return mapped
}

func (slice NumberSlice) AsyncMapBool(fn func(Number) bool, options ...NumberSliceAsyncOption) []bool {
	output := make([]bool, len(slice))
	eachFn := func(t Number, i int) {
		v := fn(t)
		output[i] = v
	}
	slice.AsyncEachIndex(eachFn, options...)
	return output
}

func (slice NumberSlice) Reversed() NumberSlice {
	r := slice.Copy()
	r.Reverse()
	return r
}

func (slice NumberSlice) Reverse() {
	for i, j := 0, len(slice)-1; i < j; i, j = i+1, j-1 {
		slice[i], slice[j] = slice[j], slice[i]
	}
}

// safe index access allows negative indexing, but if past bounds will error
func (slice NumberSlice) Item(index int) (item Number, err error) {
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

func (slice NumberSlice) ReverseSelect(where func(Number) bool, ands ...func(Number) bool) NumberSlice {
	if len(ands) > 0 {
		where = WhereNumberAll(append([]func(Number) bool{where}, ands...)...)
	}
	var selected NumberSlice
	for i := len(slice) - 1; i >= 0; i-- {
		t := slice[i]
		if where(t) {
			selected = append(selected, t)
		}
	}
	return selected
}

func (slice NumberSlice) First(where ...func(Number) bool) Number {
	hasCriteria := len(where) > 0
	matchesCriteria := WhereNumberAll(where...)
	for _, t := range slice {
		if !hasCriteria || matchesCriteria(t) {
			return t
		}
	}
	var none Number
	return none
}

func (slice NumberSlice) Last(where ...func(Number) bool) Number {
	hasCriteria := len(where) > 0
	matchesCriteria := WhereNumberAll(where...)
	for i := len(slice) - 1; i >= 0; i-- {
		t := slice[i]
		if !hasCriteria || matchesCriteria(t) {
			return t
		}
	}
	var none Number
	return none
}
func (slice NumberSlice) FirstIndex(p func(Number) bool) int {
	for i, t := range slice {
		if p(t) {
			return i
		}
	}
	return -1
}

func (slice NumberSlice) Filter(p func(Number) bool) NumberSlice {
	var selected NumberSlice
	for _, t := range slice {
		if p(t) {
			selected = append(selected, t)
		}
	}
	return selected
}

func (slice NumberSlice) IndexSelect(p func(Number) bool) []int {
	var indexes []int
	for i, t := range slice {
		if p(t) {
			indexes = append(indexes, i)
		}
	}
	return indexes
}

func (slice NumberSlice) SelectAsync(p func(Number) bool) NumberSlice {
	var selected NumberSlice
	hits := slice.AsyncMapBool(p)
	for i, t := range slice {
		if hits[i] {
			selected = append(selected, t)
		}
	}
	return selected
}

func (slice NumberSlice) String() string {
	if slice == nil {
		return fmt.Sprint(nil)
	}
	return fmt.Sprintf("[%v]", strings.Join(slice.Strings(), ", "))
}

func (slice NumberSlice) Strings() []string {
	return slice.MapString(func(x Number) string {
		return fmt.Sprintf("%v", x)
	})
}

func (slice NumberSlice) Reject(p func(Number) bool) NumberSlice {
	return slice.Filter(func(n Number) bool { return !p(n) })
}

func (slice NumberSlice) RejectAsync(p func(Number) bool) NumberSlice {
	return slice.SelectAsync(func(n Number) bool { return !p(n) })
}

func (slice NumberSlice) Reduce(operator func(Number, Number) Number, options ...NumberSliceReduceOption) Number {
	o := &NumberSliceReduceOptions{}
	for _, opt := range options {
		opt(o)
	}
	if len(slice) == 0 {
		return o.initial
	}
	result := o.initial
	for _, next := range slice {
		result = operator(result, next)
	}
	return result
}

func (slice NumberSlice) Append(items ...Number) NumberSlice {
	if slice == nil {
		var empty NumberSlice
		return append(empty, items...)
	}
	return append(slice, items...)
}

// If no predicate function parameters given returns true if slice is not empty.
// Otherwise, will return true if all predicate function parameters return true for any item in the slice
func (slice NumberSlice) Any(pl ...func(Number) bool) bool {
	if len(pl) == 0 {
		return len(slice) > 0
	}
	p := WhereNumberAll(pl...)
	for _, t := range slice {
		if p(t) {
			return true
		}
	}
	return false
}

func (slice NumberSlice) AnyNot(pl ...func(Number) bool) bool {
	return !slice.Any(pl...)
}

func (slice NumberSlice) All(p func(Number) bool) bool {
	for _, t := range slice {
		if !p(t) {
			return false
		}
	}
	return true
}

func (slice NumberSlice) AllNot(p func(Number) bool) bool {
	return !slice.All(p)
}

func (slice NumberSlice) Copy() NumberSlice {
	cp := make(NumberSlice, len(slice))
	for i := range slice {
		cp[i] = slice[i]
	}
	return cp
}

func (slice NumberSlice) Empty() bool {
	return len(slice) == 0
}

func (slice NumberSlice) NotEmpty() bool {
	return len(slice) > 0
}

func (slice NumberSlice) Count(p func(Number) bool) int {
	return len(slice.Filter(p))
}

func (slice NumberSlice) Max() Number {
	return slice.Reduce(NumberMax)
}

func NumberMax(c1 Number, c2 Number) Number {
	if c1 < c2 {
		return c2
	}
	return c1
}

func (slice NumberSlice) Min() Number {
	return slice.Reduce(NumberMin)
}

func NumberMin(c1 Number, c2 Number) Number {
	if NumberMax(c1, c2) == c1 {
		return c2
	}
	return c1
}

// MaxBy returns an element of NumberSlice containing the maximum value, when compared to other elements using a passed func defining ‘less’. In the case of multiple items being equally maximal, the last such element is returned. Returns error if no elements. See: http://clipperhouse.github.io/gen/#MaxBy
func (slice NumberSlice) MaxBy(less func(Number, Number) bool) (result Number, err error) {
	l := len(slice)
	if l == 0 {
		err = errors.New("cannot determine the MaxBy of an empty slice")
		return
	}
	m := 0
	for i := 1; i < l; i++ {
		if slice[i] != slice[m] && !less(slice[i], slice[m]) {
			m = i
		}
	}
	result = slice[m]
	return
}

// MinBy returns an element of NumberSlice containing the minimum value, when compared to other elements using a passed func defining ‘less’. In the case of multiple items being equally minimal, the first such element is returned. Returns error if no elements. See: http://clipperhouse.github.io/gen/#MinBy
func (slice NumberSlice) MinBy(less func(Number, Number) bool) (result Number, err error) {
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

func (slice NumberSlice) Average() (Number, error) {
	return NumberAverage(slice)
}

func NumberAverage(slice NumberSlice) (Number, error) {
	var result Number
	l := len(slice)
	if l == 0 {
		return result, errors.New("cannot determine Average of zero-length numeric slice")
	}
	for _, v := range slice {
		result += v
	}
	result = result / Number(l)
	return result, nil
}

func (slice NumberSlice) AverageFloat64() (float64, error) {
	return NumberAverageFloat64(slice)
}

func NumberAverageFloat64(slice NumberSlice) (float64, error) {
	var result Number
	l := len(slice)
	if l == 0 {
		return float64(result), errors.New("cannot determine Average of zero-length numeric slice")
	}
	for _, v := range slice {
		result += v
	}
	return float64(result) / float64(l), nil
}

func (slice NumberSlice) Distinct() NumberSlice {
	var result NumberSlice
	appended := make(map[Number]bool)
	for _, v := range slice {
		_, ok := appended[v]
		if !ok {
			result = append(result, v)
			appended[v] = true
		}
	}
	return result
}

func (slice NumberSlice) DistinctBy(fn func(Number, Number) bool) (result NumberSlice) {
Outer:
	for _, v := range slice {
		for _, r := range result {
			if fn(v, r) {
				continue Outer
			}
		}
		result = append(result, v)
	}
	return result
}

func (slice NumberSlice) Each(f func(Number)) {
	for _, t := range slice {
		f(t)
	}
}

func WithNumberAsyncPoolSize(size int) NumberSliceAsyncOption {
	return func(options *NumberSliceAsyncOptions) {
		options.PoolSize = size
	}
}

func newNumberSliceAsyncOptions(opts ...NumberSliceAsyncOption) *NumberSliceAsyncOptions {
	o := &NumberSliceAsyncOptions{PoolSize: -1}
	for _, opt := range opts {
		opt(o)
	}
	return o
}

func (slice NumberSlice) AsyncEachIndex(f func(Number, int), options ...NumberSliceAsyncOption) {
	o := newNumberSliceAsyncOptions(options...)
	if o.PoolSize <= 0 {
		wg := &sync.WaitGroup{}
		for index, item := range slice {
			wg.Add(1)
			go func(item Number, index int) {
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
		go func(slice NumberSlice, f func(Number, int), pending <-chan int, completed chan<- int) {
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
	return
}

func (slice NumberSlice) AsyncEach(f func(Number), options ...NumberSliceAsyncOption) {
	slice.AsyncEachIndex(func(t Number, _ int) {
		f(t)
	}, options...)
}

func (slice NumberSlice) EachIndex(f func(Number, int)) {
	for i, t := range slice {
		f(t, i)
	}
}

func (slice NumberSlice) Equal(other []Number) bool {
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
func (slice NumberSlice) Len() int {
	return len(slice)
}

func (slice NumberSlice) Less(i, j int) bool {
	return slice[i] < slice[j]
}

func (slice NumberSlice) Replace(fn func(t Number) Number) {
	for i, t := range slice {
		slice[i] = fn(t)
	}
}

func (slice NumberSlice) AsyncReplace(fn func(t Number) Number, options ...NumberSliceAsyncOption) {
	slice.AsyncEachIndex(func(t Number, i int) {
		slice[i] = fn(t)
	}, options...)
}

func (slice NumberSlice) Swap(i, j int) {
	slice[i], slice[j] = slice[j], slice[i]
}

func (slice NumberSlice) Sum() (result Number) {
	for _, v := range slice {
		result += v
	}
	return
}

// Shuffled returns a copy of NumberSlice with the contents shuffles  using a version of the Fisher-Yates shuffle. See: http://clipperhouse.github.io/gen/#Shuffle
func (slice NumberSlice) Shuffled() NumberSlice {
	s := slice.Copy()
	s.Shuffle()
	return s
}

// Shuffle shuffles the contents of NumberSlice in place using a version of the Fisher-Yates shuffle. See: http://clipperhouse.github.io/gen/#Shuffle
func (slice NumberSlice) Shuffle() {
	total := len(slice)
	for i := 0; i < total; i++ {
		r := i + rand.Intn(total-i)
		slice[r], slice[i] = slice[i], slice[r]
	}
}

func (slice NumberSlice) Sort() {
	sort.Sort(slice)
}

func (slice NumberSlice) Sorted() NumberSlice {
	cp := slice.Copy()
	cp.Sort()
	return cp
}

func (slice NumberSlice) SortDesc() {
	sort.Sort(__NumberSliceDesc(slice))
}

func (slice NumberSlice) SortedDesc() NumberSlice {
	s := slice.Copy()
	s.SortDesc()
	return s
}

func (slice NumberSlice) SortedBy(less func(Number, Number) bool) NumberSlice {
	s := slice.Copy()
	s.SortBy(less)
	return s
}

func (slice NumberSlice) SortBy(less func(Number, Number) bool) {
	// Switch to heapsort if depth of 2*ceil(lg(n+1)) is reached.
	n := len(slice)
	maxDepth := 0
	for i := n; i > 0; i >>= 1 {
		maxDepth++
	}
	maxDepth *= 2
	quickSortNumberSlice(slice, less, 0, n, maxDepth)
}

func (slice NumberSlice) IsSortedBy(less func(Number, Number) bool) bool {
	n := len(slice)
	for i := n - 1; i > 0; i-- {
		if less(slice[i], slice[i-1]) {
			return false
		}
	}
	return true
}

func (slice NumberSlice) SortDescBy(less func(Number, Number) bool) {
	slice.SortBy(func(a Number, b Number) bool { return !less(a, b) })
}

func (slice NumberSlice) SortedDescBy(less func(Number, Number) bool) NumberSlice {
	greater := func(a, b Number) bool {
		return less(b, a)
	}
	return slice.SortedBy(greater)
}

func (slice NumberSlice) Split(fn func(n Number) bool) (NumberSlice, NumberSlice) {
	var a NumberSlice
	var b NumberSlice
	for _, n := range slice {
		if fn(n) {
			a = append(a, n)
		} else {
			b = append(b, n)
		}
	}
	return a, b
}

func (slice NumberSlice) IsSortedDescBy(less func(Number, Number) bool) bool {
	greater := func(a, b Number) bool {
		return less(b, a)
	}
	return slice.IsSortedBy(greater)
}

func (slice NumberSlice) AnyGreater(n Number) bool {
	for _, sn := range slice {
		if sn > n {
			return true
		}
	}
	return false
}

func (slice NumberSlice) AnyLess(n Number) bool {
	for _, sn := range slice {
		if sn < n {
			return true
		}
	}
	return false
}

func (slice NumberSlice) AnyGreaterEqual(n Number) bool {
	for _, sn := range slice {
		if sn >= n {
			return true
		}
	}
	return false
}

func (slice NumberSlice) AnyLessEqual(n Number) bool {
	for _, sn := range slice {
		if sn <= n {
			return true
		}
	}
	return false
}

func (slice NumberSlice) AnyEqual(n Number) bool {
	for _, sn := range slice {
		if sn == n {
			return true
		}
	}
	return false
}

func (slice NumberSlice) ContainsAll(items ...Number) bool {
	for _, item := range items {
		if !slice.AnyEqual(item) {
			return false
		}
	}
	return true
}

func (slice NumberSlice) ContainsAny(items ...Number) bool {
	for _, item := range items {
		if slice.AnyEqual(item) {
			return true
		}
	}
	return false
}

func (slice NumberSlice) Contains(n Number) bool {
	return slice.AnyEqual(n)
}

func (slice NumberSlice) SkipTake(skip, take int) NumberSlice {
	var out NumberSlice
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
func swapNumberSlice(slice NumberSlice, a, b int) {
	slice[a], slice[b] = slice[b], slice[a]
}

// Insertion sort
func insertionSortNumberSlice(slice NumberSlice, less func(Number, Number) bool, a, b int) {
	for i := a + 1; i < b; i++ {
		for j := i; j > a && less(slice[j], slice[j-1]); j-- {
			swapNumberSlice(slice, j, j-1)
		}
	}
}

// siftDown implements the heap property on slice[lo, hi).
// first is an offset into the array where the root of the heap lies.
func siftDownNumberSlice(slice NumberSlice, less func(Number, Number) bool, lo, hi, first int) {
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
		swapNumberSlice(slice, first+root, first+child)
		root = child
	}
}
func heapSortNumberSlice(slice NumberSlice, less func(Number, Number) bool, a, b int) {
	first := a
	lo := 0
	hi := b - a
	// Build heap with greatest element at top.
	for i := (hi - 1) / 2; i >= 0; i-- {
		siftDownNumberSlice(slice, less, i, hi, first)
	}
	// Pop elements, largest first, into end of slice.
	for i := hi - 1; i >= 0; i-- {
		swapNumberSlice(slice, first, first+i)
		siftDownNumberSlice(slice, less, lo, i, first)
	}
}

// Quicksort, following Bentley and McIlroy,
// Engineering a Sort Function, SP&E November 1993.
// medianOfThree moves the median of the three values slice[a], slice[b], slice[c] into slice[a].
func medianOfThreeNumberSlice(slice NumberSlice, less func(Number, Number) bool, a, b, c int) {
	m0 := b
	m1 := a
	m2 := c
	// bubble sort on 3 elements
	if less(slice[m1], slice[m0]) {
		swapNumberSlice(slice, m1, m0)
	}
	if less(slice[m2], slice[m1]) {
		swapNumberSlice(slice, m2, m1)
	}
	if less(slice[m1], slice[m0]) {
		swapNumberSlice(slice, m1, m0)
	}
	// now slice[m0] <= slice[m1] <= slice[m2]
}
func swapRangeNumberSlice(slice NumberSlice, a, b, n int) {
	for i := 0; i < n; i++ {
		swapNumberSlice(slice, a+i, b+i)
	}
}
func doPivotNumberSlice(slice NumberSlice, less func(Number, Number) bool, lo, hi int) (midlo, midhi int) {
	m := lo + (hi-lo)/2 // Written like this to avoid integer overflow.
	if hi-lo > 40 {
		// Tukey's Ninther, median of three medians of three.
		s := (hi - lo) / 8
		medianOfThreeNumberSlice(slice, less, lo, lo+s, lo+2*s)
		medianOfThreeNumberSlice(slice, less, m, m-s, m+s)
		medianOfThreeNumberSlice(slice, less, hi-1, hi-1-s, hi-1-2*s)
	}
	medianOfThreeNumberSlice(slice, less, lo, m, hi-1)
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
				swapNumberSlice(slice, a, b)
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
				swapNumberSlice(slice, c-1, d-1)
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
		swapNumberSlice(slice, b, c-1)
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
	swapRangeNumberSlice(slice, lo, b-n, n)
	n = min(hi-d, d-c)
	swapRangeNumberSlice(slice, c, hi-n, n)
	return lo + b - a, hi - (d - c)
}

func quickSortNumberSlice(slice NumberSlice, less func(Number, Number) bool, a, b, maxDepth int) {
	for b-a > 7 {
		if maxDepth == 0 {
			heapSortNumberSlice(slice, less, a, b)
			return
		}
		maxDepth--
		mlo, mhi := doPivotNumberSlice(slice, less, a, b)
		// Avoiding recursion on the larger subproblem guarantees
		// a stack depth of at most lg(b-a).
		if mlo-a < b-mhi {
			quickSortNumberSlice(slice, less, a, mlo, maxDepth)
			a = mhi // i.e., quickSortNumberSlice(slice, mhi, b)
		} else {
			quickSortNumberSlice(slice, less, mhi, b, maxDepth)
			b = mlo // i.e., quickSortNumberSlice(slice, a, mlo)
		}
	}
	if b-a > 1 {
		insertionSortNumberSlice(slice, less, a, b)
	}
}

type __NumberSliceDesc []Number

func (slice __NumberSliceDesc) Len() int {
	return len(slice)
}

//actually greater!
func (slice __NumberSliceDesc) Less(i, j int) bool {
	return slice[i] > slice[j]
}

func (slice __NumberSliceDesc) Swap(i, j int) {
	slice[i], slice[j] = slice[j], slice[i]
}
