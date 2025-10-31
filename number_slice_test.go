package collex

import (
	"math/rand"
	"testing"
	"time"

	"github.com/bradfitz/iter"
	. "github.com/onsi/gomega"
	"github.com/mwelles/suite"
)

func TestNumberSliceSuite(t *testing.T) {
	suite.Run(t, new(NumberSliceSuite))
}

type NumberSliceSuite struct {
	suite.StandaloneSuite
}

func (s *NumberSliceSuite) SetupSuite() {
	s.StandaloneSuite.SetupSuite()
	rand.Seed(time.Now().UnixNano())
}

func (s *NumberSliceSuite) TestAsyncEachIndex() {
	n := 200
	minSleep := 1
	maxExtraSleep := 50
	input := make(NumberSlice, n)
	output := make(NumberSlice, n)
	for i := range iter.N(n) {
		input[i] = Number(i)
	}
	fn := func(n Number, i int) {
		extraSleep := rand.Intn(maxExtraSleep)
		time.Sleep(time.Duration(extraSleep+minSleep) * time.Millisecond)
		output[i] = n * n
	}
	s.G.Describe("NumberSlice.AsyncEachIndex(func(Number, int))", func() {
		input.AsyncEachIndex(fn, WithNumberAsyncPoolSize(n))
		s.G.It("all async each functions will have completed when AsyncEachIndex returns", func() {
			for i := range input {
				Expect(output[i]).To(Equal(input[i] * input[i]))
			}
		})
		s.G.It("index supplied to the function should match the index of the item in the slice", func() {
			for i := range input {
				Expect(output[i]).To(Equal(input[i] * input[i]))
			}
		})
	})

}

func (s *NumberSliceSuite) TestDistinct() {
	input := NumberSlice{1, 2, 3, 4, 1, 2, 3, 4}
	output := input.Distinct()
	seen := make(map[Number]bool)
	s.G.Describe("NumberSlice Distinct()", func() {
		s.G.It("should should remove all duplicate values", func() {
			Expect(len(input) > len(output)).To(BeTrue())
			for _, o := range output {
				_, ok := seen[o]
				Expect(ok).To(BeFalse(), "duplicate item '%s' in results", o)
				seen[o] = true
			}
		})
	})
}

func (s *NumberSliceSuite) TestSelectAsync() {
	matches := NumberSlice{2, 4, 6, 9, 11, 22, 23, 25}
	fn := func(n Number) bool {
		for _, m := range matches {
			if m == n {
				return true
			}
		}
		return false
	}
	input := NumberSlice{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25}

	s.G.Describe("NumberSlice.SelectAsync(func(Number) bool)", func() {
		output := input.SelectAsync(fn)
		s.G.It("should return only matching values", func() {
			Expect(len(output)).To(Equal(len(matches)))
		})
		s.G.It("should return matching values in the correct order", func() {
			lastIndex := 0
			for _, o := range output {
				index := input.FirstIndex(func(n Number) bool { return o == n })
				Expect(index >= lastIndex).To(BeTrue(), "index %d is not greater or equal to last index %d", index, lastIndex)
			}
		})
	})

}

func (s *NumberSliceSuite) TestAnyNot() {
	s.G.Describe("NumberSlice.AnyNot(...func(Number) bool)", func() {
		s.G.Describe("When called with no parameters", func() {
			slice := NewNumberSlice()
			s.G.It("Should return true when slice is empty", func() {
				Expect(slice.AnyNot()).To(BeTrue())
			})
			s.G.It("Should return false when slice is not-empty", func() {
				slice = append(slice, 1)
				Expect(slice.AnyNot()).To(BeFalse())
			})
		})
		matchAny := func(_ Number) bool {
			return true
		}
		match2 := func(t Number) bool {
			return t == 2
		}
		match3 := func(t Number) bool {
			return t == 3
		}
		match999 := func(t Number) bool {
			return t == 999
		}

		s.G.Describe("When called with a single predicate function parameter", func() {
			slice := NewNumberSlice(1, 2, 3)
			s.G.It("Should return false if any item in list matches", func() {
				Expect(slice.AnyNot(match2)).To(BeFalse())
				Expect(slice.AnyNot(match3)).To(BeFalse())
			})
			s.G.It("Should return true if no item in list matches", func() {
				Expect(slice.AnyNot(match999)).To(BeTrue())
			})
		})

		s.G.Describe("When called with multiple predicate function parameters", func() {
			slice := NewNumberSlice(1, 2, 3)
			s.G.It("Should return false if any item in list matches ALL predicate parameters", func() {
				Expect(slice.AnyNot(match2, matchAny)).To(BeFalse())
			})
			s.G.It("Should return true if no item in list matches ALL predicate parameters", func() {
				Expect(slice.AnyNot(match2, match3)).To(BeTrue())
			})
		})

	})
}

func (s *NumberSliceSuite) TestAny() {
	s.G.Describe("NumberSlice.Any(...func(Number) bool)", func() {
		s.G.Describe("When called with no parameters", func() {
			slice := NewNumberSlice()
			s.G.It("Should return false when slice is empty", func() {
				Expect(slice.Any()).To(BeFalse())
			})
			s.G.It("Should return true when slice is not-empty", func() {
				slice = append(slice, 1)
				Expect(slice.Any()).To(BeTrue())
			})
		})
		matchAny := func(_ Number) bool {
			return true
		}
		match2 := func(t Number) bool {
			return t == 2
		}
		match3 := func(t Number) bool {
			return t == 3
		}
		match999 := func(t Number) bool {
			return t == 999
		}

		s.G.Describe("When called with a single predicate function parameter", func() {
			slice := NewNumberSlice(1, 2, 3)
			s.G.It("Should return true if any item in list matches", func() {
				Expect(slice.Any(match2)).To(BeTrue())
				Expect(slice.Any(match3)).To(BeTrue())
			})
			s.G.It("Should return false if no item in list matches", func() {
				Expect(slice.Any(match999)).To(BeFalse())
			})
		})

		s.G.Describe("When called with multiple predicate function parameters", func() {
			slice := NewNumberSlice(1, 2, 3)
			s.G.It("Should return true if any item in list matches ALL predicate parameters", func() {
				Expect(slice.Any(match2, matchAny)).To(BeTrue())
			})
			s.G.It("Should return false if no item in list matches ALl predicate parameters", func() {
				Expect(slice.Any(match2, match3)).To(BeFalse())
			})
		})
	})
}
