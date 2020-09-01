package main

type Rectangle struct {
    Width, Height int
}

ghost
requires acc(r.Width)
ensures acc(r.Width)
pure func (r *Rectangle) GetWidth() (res int) {
    return r.Width
}

func main() {
    r! := Rectangle{Width: 2, Height: 5}
    w := r.GetWidth()
    assert (*(Rectangle)).GetWidth(&r) == w && w == 2
}