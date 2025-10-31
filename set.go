package collex

import (
	"github.com/noho-digital/mapset"
)

// reset these in an init in the dest package if you dont want the defaults
var __TypeSetReceiverAutoConvertComparisonTypeSetsToMatchingThreadSafeUnsafeVariants = true

//
//type Iterator struct {
//	*mapset.Iterator
//}

type ReadOnlyTypeSet interface {

	// Note that the argument to all methods that
	// take a ReadOnlyTypeSet or TypeSet as arguments
	// must pass a set that is of the same thread safe / unsafe variant
	// as the receiver of the method or one of two things will happen:
	//
	//      - the receiever will create a copy of the comparison set that is of the same thread
	//        safe / unsafe type variant as itself, and use it in the operation.
	//
	//   OR
	//       - it will panic.
	// This behavior is controlled by the value of:
	//
	// __TypeSetReceiverAutoConvertComparisonTypeSetsToMatchingThreadSafeUnsafeVariants
	//
	// The default is true, which means expensive copies will be performed
	//
	// This can be be overridden at run in an init() function
	// in the package that TypeSet is generated into.

	// Synonym for Cardinality() for folks more familar with go than set theory
	Len() int

	// Returns the number of elements in the set.
	Cardinality() int

	// Returns a clone of the set using the same
	// implementation, duplicating all keys.
	Clone() TypeSet

	// Returns whether the given items
	// are all in the set.
	Contains(i ...Type) bool

	// Returns if the given item is not in the set
	NotContains(i Type) bool

	// Returns whether any the given items
	// are not in the set
	NotContainsAny(i ...Type) bool

	// Returns whether any any given items
	// in the set.
	ContainsAny(i ...Type) bool

	// Returns whether any given items
	// are all in the set.
	ContainsAll(i ...Type) bool

	// Returns the difference between this set
	// and other. The returned set will contain
	// all elements of this set that are not also
	// elements of other.
	Difference(other ReadOnlyTypeSet) TypeSet

	// Determines if two sets are equal to each
	// other. If they have the same cardinality
	// and contain the same elements, they are
	// considered equal. The order in which
	// the elements were added is irrelevant.
	//
	Equal(other ReadOnlyTypeSet) bool

	//
	// !set.Equal(other)
	//
	NotEqual(other ReadOnlyTypeSet) bool

	// Returns true if there are
	// any elements that exist in both sets
	Intersects(other ReadOnlyTypeSet) bool

	// Returns a new set containing only the elements
	// that exist only in both sets.
	Intersect(other ReadOnlyTypeSet) TypeSet

	// Returns true if there is no
	// elements that exist both in the
	// receiver set and the argument
	IsDisjoint(other ReadOnlyTypeSet) bool

	// Determines if every element in this set is in
	// the other set but the two sets are not equal.
	IsProperSubset(other ReadOnlyTypeSet) bool

	// Determines if every element in the other set
	// is in this set but the two sets are not
	// equal.
	IsProperSuperset(other ReadOnlyTypeSet) bool

	// Determines if every element in this set is in
	// the other set.
	IsSubset(other ReadOnlyTypeSet) bool

	// Determines if every element in the other set
	// is in this set.
	IsSuperset(other ReadOnlyTypeSet) bool

	// Iterates over elements and executes the passed func against each element.
	// If passed func returns true, stop iteration at the time.
	Each(func(Type) bool)

	String() string

	// Returns a new set with all elements in both sets.
	Union(other ReadOnlyTypeSet) TypeSet

	// Returns the Cartesian Product of two sets.
	CartesianProduct(other ReadOnlyTypeSet) TypeSet
	// Returns the members of the set as a slice.
	ToSlice() []Type

	// Returns true if the receiver is not empty and it contains the argument item
	NotEmptyAndContains(item Type) bool

	// Returns true if the receiver is not empty and does not contain argument item
	NotEmptyAndNotContains(item Type) bool

	// Returns true if the receiver is empty (i.e. if Cardinality() == 0)
	Empty() bool
	// Returns true if the receiver id not empty (i.e. if Cardinality() > 0)
	NotEmpty() bool

	// Returns true if the receiver is nil
	Nil() bool

	// Returns true if the receiver is not nil
	NotNil() bool

	// Returns a new set with all elements which are
	// in either this set or the other set but not in both.
	SymmetricDifference(other ReadOnlyTypeSet) TypeSet

	// Returns all subsets of a given set (Power Set).
	PowerSet() TypeSet

	// Returns true if reciver is thread safe type variant,
	// wil be true if created with the NewTypeSet() and NewTypeSetFromSlice()
	// constructs, will be false if it was created with the
	// NewThreadUnsafeTypeSet(0 and NewThreadUnsafeTypeSetFromSlice() constructors
	IsThreadSafe() bool

	// Returns the backing untyped mapset.Set interface{} set reciever wraps
	MapsetSet() mapset.Set
}

type TypeSet interface {
	ReadOnlyTypeSet

	// Adds an element to the set. Returns whether
	// the item was added.
	Add(i Type) bool

	// Adds all the items specified as arguments to the set
	// Returns an array of booleans indicating which of the items
	// was added.
	AddAll(items ...Type) []bool

	// Removes all elements from the set, leaving
	// the empty set.
	Clear()

	// Remove a single element from the set.
	Remove(i Type)

	// Pop removes and returns an arbitrary item from the set.
	Pop() Type
}

type mapsetTypeSet struct {
	ms           mapset.Set
	isThreadSafe bool
}

func (s *mapsetTypeSet) NotContains(i Type) bool {
	if s == nil {
		return false
	}
	return !s.Contains(i)
}

func (s *mapsetTypeSet) NotContainsAny(tt ...Type) bool {
	for _, t := range tt {
		if !s.Contains(t) {
			return true
		}
	}
	return false
}

func (s *mapsetTypeSet) Nil() bool {
	return s == nil
}

func (s *mapsetTypeSet) NotNil() bool {
	return s != nil
}

func (s *mapsetTypeSet) IsDisjoint(other ReadOnlyTypeSet) bool {
	switch {
	case s == nil || other == nil:
		return false
	case s.IsThreadSafe() != other.IsThreadSafe():
		return !s.Intersects(other)
	default:
		return s.MapsetSet().Intersect(other.MapsetSet()).Cardinality() == 0
	}
}

func (s *mapsetTypeSet) Intersects(o ReadOnlyTypeSet) bool {
	if o == nil || s == nil {
		return false
	}
	return s.ContainsAny(o.ToSlice()...)
}

func (s *mapsetTypeSet) ContainsAny(items ...Type) bool {
	if s == nil {
		return false
	}
	for _, i := range items {
		if s.ms.Contains(i) {
			return true
		}
	}
	return false
}

func (s *mapsetTypeSet) ContainsAll(i ...Type) bool {
	return s.Contains(i...)
}

func (s *mapsetTypeSet) MapsetSet() mapset.Set {
	if s == nil {
		return nil
	}
	return s.ms
}

func (s *mapsetTypeSet) Add(i Type) bool {
	return s.ms.Add(i)
}

func (s *mapsetTypeSet) AddAll(il ...Type) []bool {
	var rl []bool
	for _, i := range il {
		rl = append(rl, s.ms.Add(i))
	}
	return rl
}

func (s *mapsetTypeSet) Len() int {
	return s.ms.Cardinality()
}

func (s *mapsetTypeSet) Cardinality() int {
	return s.ms.Cardinality()
}

func (s *mapsetTypeSet) Clear() {
	s.ms.Clear()
}

func (s *mapsetTypeSet) Clone() TypeSet {
	if s == nil {
		return nil
	}
	return &mapsetTypeSet{ms: s.ms.Clone(), isThreadSafe: s.isThreadSafe}
}

func (s *mapsetTypeSet) Contains(t ...Type) bool {
	if s == nil {
		return false
	}
	i := __convertTypeSliceToInterfaceSlice(t)
	return s.ms.Contains(i...)
}

func (s *mapsetTypeSet) Difference(other ReadOnlyTypeSet) TypeSet {
	other = __autoConvertToThreadSafeUnsafeTypeSetMatchingCopyIfEnabled(s, other)
	return &mapsetTypeSet{ms: s.ms.Difference(other.MapsetSet()), isThreadSafe: s.isThreadSafe}
}

func (s *mapsetTypeSet) Equal(other ReadOnlyTypeSet) bool {
	if s == nil {
		return s == other
	}
	other = __autoConvertToThreadSafeUnsafeTypeSetMatchingCopyIfEnabled(s, other)
	return s.ms.Equal(other.MapsetSet())
}

func (s *mapsetTypeSet) NotEqual(other ReadOnlyTypeSet) bool {
	return !s.ms.Equal(other.MapsetSet())
}

func (s *mapsetTypeSet) Intersect(other ReadOnlyTypeSet) TypeSet {
	other = __autoConvertToThreadSafeUnsafeTypeSetMatchingCopyIfEnabled(s, other)
	ms := s.MapsetSet().Intersect(other.MapsetSet())
	return &mapsetTypeSet{ms: ms, isThreadSafe: s.isThreadSafe}
}

func (s *mapsetTypeSet) IsProperSubset(other ReadOnlyTypeSet) bool {
	other = __autoConvertToThreadSafeUnsafeTypeSetMatchingCopyIfEnabled(s, other)
	return s.ms.IsProperSubset(other.MapsetSet())
}

func (s *mapsetTypeSet) IsProperSuperset(other ReadOnlyTypeSet) bool {
	other = __autoConvertToThreadSafeUnsafeTypeSetMatchingCopyIfEnabled(s, other)
	return s.ms.IsProperSuperset(other.MapsetSet())
}

func (s *mapsetTypeSet) IsSubset(other ReadOnlyTypeSet) bool {
	other = __autoConvertToThreadSafeUnsafeTypeSetMatchingCopyIfEnabled(s, other)
	return s.ms.IsSubset(other.MapsetSet())
}

func (s *mapsetTypeSet) IsSuperset(other ReadOnlyTypeSet) bool {
	other = __autoConvertToThreadSafeUnsafeTypeSetMatchingCopyIfEnabled(s, other)
	return s.ms.IsSuperset(other.MapsetSet())
}

func (s *mapsetTypeSet) Each(f func(Type) bool) {
	fi := func(i interface{}) bool {
		t, ok := i.(Type)
		if !ok {
			return false
		}
		return f(t)

	}
	s.ms.Each(fi)
}

func (s *mapsetTypeSet) IsThreadSafe() bool {
	return s.isThreadSafe
}

func (s *mapsetTypeSet) Remove(i Type) {
	s.ms.Remove(i)
}

func (s *mapsetTypeSet) String() string {
	return s.ms.String()
}

func (s *mapsetTypeSet) SymmetricDifference(other ReadOnlyTypeSet) TypeSet {
	return &mapsetTypeSet{ms: s.ms.SymmetricDifference(other.MapsetSet()), isThreadSafe: s.isThreadSafe}
}

func (s *mapsetTypeSet) Union(other ReadOnlyTypeSet) TypeSet {
	switch {
	case s != nil && other != nil:
		other = __autoConvertToThreadSafeUnsafeTypeSetMatchingCopyIfEnabled(s, other)
		return &mapsetTypeSet{ms: s.ms.Union(other.MapsetSet()), isThreadSafe: s.isThreadSafe}
	case s == nil:
		if other == nil {
			return nil
		}
		return other.Union(__emptyTypeSetMatchingType(other))
	default:
		return s.Union(__emptyTypeSetMatchingType(s))
	}
}

func (s *mapsetTypeSet) Pop() Type {
	var def Type
	i := s.ms.Pop()
	if i == nil {
		return def
	}
	return __convertInterfaceToType(i)
}

func (s *mapsetTypeSet) PowerSet() TypeSet {
	return &mapsetTypeSet{ms: s.ms.PowerSet(), isThreadSafe: s.isThreadSafe}
}

func (s *mapsetTypeSet) CartesianProduct(other ReadOnlyTypeSet) TypeSet {
	other = __autoConvertToThreadSafeUnsafeTypeSetMatchingCopyIfEnabled(s, other)
	return &mapsetTypeSet{ms: s.ms.CartesianProduct(other.MapsetSet()), isThreadSafe: s.isThreadSafe}
}

func (s *mapsetTypeSet) ToSlice() []Type {
	if s == nil {
		return nil
	}
	return ___convertInterfaceSliceToTypeSlice(s.ms.ToSlice())
}

func (s *mapsetTypeSet) NotEmptyAndContains(item Type) bool {
	return (!s.Empty()) && s.Contains(item)
}

func (s *mapsetTypeSet) NotEmptyAndNotContains(item Type) bool {
	return (!s.Empty()) && (!s.Contains(item))
}

func (s *mapsetTypeSet) NotEmpty() bool {
	return s.Cardinality() > 0
}

func (s *mapsetTypeSet) Empty() bool {
	return s.Cardinality() == 0
}

func (s *mapsetTypeSet) AddItems(items ...Type) int {
	n := 0
	for _, i := range items {
		if s.Add(i) {
			n++
		}
	}
	return n
}

// NewInterfaceSet creates and returns a reference to an empty set.  Operations
// on the resulting set are thread-safe.
func NewTypeSet(items ...Type) TypeSet {
	return newMapsetTypeSet(items...)
}

func newMapsetTypeSet(items ...Type) *mapsetTypeSet {
	ms := mapset.NewSet()
	for _, t := range items {
		ms.Add(t)
	}
	return &mapsetTypeSet{ms: ms, isThreadSafe: true}
}

// NewTypeSetFromSlice creates and returns a reference to a
// set from an existing slice.  Operations on the resulting set are
// thread-safe.
func NewTypeSetFromSlice(s []Type) TypeSet {
	i := __convertTypeSliceToInterfaceSlice(s)
	return &mapsetTypeSet{ms: mapset.NewSetFromSlice(i), isThreadSafe: true}
}

// NewThreadUnsafeTypeSet creates and returns a reference to either an empty set from a slice composed of the
// optional arguments.
func NewThreadUnsafeTypeSet(i ...Type) TypeSet {
	ms := mapset.NewThreadUnsafeSet()
	for _, t := range i {
		ms.Add(t)
	}
	return &mapsetTypeSet{ms: ms, isThreadSafe: false}
}

// NewThreadUnsafeSetFromSlice creates and returns a reference to a
// set from an existing slice.  Operations on the resulting set are
// not thread-safe.
func NewThreadUnsafeTypeSetFromSlice(s []Type) TypeSet {
	i := __convertTypeSliceToInterfaceSlice(s)
	return &mapsetTypeSet{ms: mapset.NewThreadUnsafeSetFromSlice(i), isThreadSafe: false}
}

func __ensureThreadSafeTypeSet(other ReadOnlyTypeSet) ReadOnlyTypeSet {
	if other.IsThreadSafe() {
		return other
	}
	return NewTypeSetFromSlice(other.ToSlice())
}

func __ensureThreadUnsafeTypeSet(other ReadOnlyTypeSet) ReadOnlyTypeSet {
	if other.IsThreadSafe() {
		return NewThreadUnsafeTypeSetFromSlice(other.ToSlice())
	}
	return other
}
func __autoConvertToThreadSafeUnsafeTypeSetMatchingCopyIfEnabled(s, other ReadOnlyTypeSet) ReadOnlyTypeSet {
	if !__TypeSetReceiverAutoConvertComparisonTypeSetsToMatchingThreadSafeUnsafeVariants {
		return other
	}
	if s.IsThreadSafe() {
		return __ensureThreadSafeTypeSet(other)
	}

	return __ensureThreadUnsafeTypeSet(other)
}

func __convertTypeSliceToInterfaceSlice(typeSlice []Type) []interface{} {
	interfaceSlice := make([]interface{}, len(typeSlice))
	for i := range typeSlice {
		interfaceSlice[i] = typeSlice[i]
	}
	return interfaceSlice
}

func __convertInterfaceToType(item interface{}) Type {
	t, ok := item.(Type)
	if !ok {
		panic("item is not correct type")
	}
	return t
}

func ___convertInterfaceSliceToTypeSlice(interfaceSlice []interface{}) []Type {
	typeSlice := make([]Type, len(interfaceSlice))
	for i, item := range interfaceSlice {
		typeSlice[i] = __convertInterfaceToType(item)
	}
	return typeSlice
}

func __emptyTypeSetMatchingType(s ReadOnlyTypeSet) ReadOnlyTypeSet {
	if s.IsThreadSafe() {
		return __emptyTypeSet
	} else {
		return __emptyThreadUnsafeTypeSet
	}
}

var __emptyTypeSet = NewTypeSet()
var __emptyThreadUnsafeTypeSet = NewThreadUnsafeTypeSet()
