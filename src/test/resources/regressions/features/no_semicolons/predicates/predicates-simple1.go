
package pkg;

type coordinate struct{
    x, y, val int
}

pred cooMem(self *coordinate) {
    acc(self.x) && acc(self.y) && acc(self.val)
}


requires cooMem(self)
ensures  cooMem(self)
pure func (self *coordinate) value() int {
    return unfolding cooMem(self) in self.val
}

func test1() {
    coo := &coordinate{1,2,3}
    fold cooMem(coo)
    assert coo.value() == 3
    unfold cooMem(coo)
    assert coo.val == 3

    //:: ExpectedOutput(assert_error:assertion_error)
    assert false
}
