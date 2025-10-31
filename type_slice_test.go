package collex

import (
	"testing"
)

func TestTypeSliceAnyNot(t *testing.T) {
	t.Run("empty slice", func(t *testing.T) {
		slice := NewTypeSlice()
		if !slice.AnyNot() {
			t.Error("AnyNot() should return true for empty slice")
		}
	})

	t.Run("non-empty slice with no predicates", func(t *testing.T) {
		slice := NewTypeSlice("a")
		if slice.AnyNot() {
			t.Error("AnyNot() should return false for non-empty slice with no predicates")
		}
	})

	t.Run("single predicate", func(t *testing.T) {
		slice := NewTypeSlice("a", "b", "c")
		matchB := func(t Type) bool { return t == "b" }
		matchZ := func(t Type) bool { return t == "z" }

		if slice.AnyNot(matchB) {
			t.Error("AnyNot(matchB) should return false when item matches")
		}
		if !slice.AnyNot(matchZ) {
			t.Error("AnyNot(matchZ) should return true when no item matches")
		}
	})
}

func TestTypeSliceAny(t *testing.T) {
	t.Run("empty slice", func(t *testing.T) {
		slice := NewTypeSlice()
		if slice.Any() {
			t.Error("Any() should return false for empty slice")
		}
	})

	t.Run("non-empty slice with no predicates", func(t *testing.T) {
		slice := NewTypeSlice("a")
		if !slice.Any() {
			t.Error("Any() should return true for non-empty slice with no predicates")
		}
	})

	t.Run("single predicate", func(t *testing.T) {
		slice := NewTypeSlice("a", "b", "c")
		matchB := func(t Type) bool { return t == "b" }
		matchZ := func(t Type) bool { return t == "z" }

		if !slice.Any(matchB) {
			t.Error("Any(matchB) should return true when item matches")
		}
		if slice.Any(matchZ) {
			t.Error("Any(matchZ) should return false when no item matches")
		}
	})
}