package collex

import (
	"testing"
	"github.com/mwelles/suite"
)

func TestSetSuite(t *testing.T) {
	suite.Run(t, new(SetSuite))
}

type SetSuite struct {
	suite.Suite
}

func (s *SetSuite) TestIsThreadSafeIntrospection() {
	unsafes := []TypeSet{
		NewThreadUnsafeTypeSet(),
		NewThreadUnsafeTypeSetFromSlice([]Type{}),
	}
	safes := []TypeSet{
		NewTypeSet(),
		NewTypeSetFromSlice([]Type{}),
	}

	for _, unsafe := range unsafes {
		s.Assert().False(unsafe.IsThreadSafe(), "unsafe should return false for IsThreadSafe()")
	}

	for _, safe := range safes {
		s.Assert().True(safe.IsThreadSafe(), "safe should return true for IsThreadSafe()")
	}
}

func (s *SetSuite) TestThreadSafeDifferenceThreadUnsafe() {
	//if !__TypeSetReceiverAutoConvertComparisonTypeSetsToMatchingThreadSafeUnsafeVariants {
	//s.T().Skip("auto conversion disabled")
	//}
	ts := NewThreadUnsafeTypeSet()
	tus := NewThreadUnsafeTypeSet()

	ds := ts.Difference(tus)
	s.Require().NotNil(ds)
}
