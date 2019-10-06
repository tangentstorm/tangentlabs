// this was just something i was experimenting with on the subway.
// I now have a real chess related program in go here:
// https://github.com/tangentstorm/chesscoach

package main

import "fmt"

var board = [][]byte{
	{11, 9, 10, 13, 12, 10, 9, 11}, // [0]=8
	{8, 8, 8, 8, 8, 8, 8, 8},       // [1]=7
	{0, 0, 0, 0, 0, 0, 0, 0},       // [2]=6
	{0, 0, 0, 0, 0, 0, 0, 0},       // [3]=5
	{0, 0, 0, 0, 0, 0, 0, 0},       // [4]=4
	{0, 0, 0, 0, 0, 0, 0, 0},       // [5]=3
	{1, 1, 1, 1, 1, 1, 1, 1},       // [6]=2
	{4, 2, 3, 5, 6, 2, 3, 4}}       // [7]=1

var symbol = ".PBNRQK-pbnrqk" // WHITE,black
var rank = []byte{0, 7, 6, 5, 4, 3, 2, 1, 0} // skip 1 at start because there's no rank 0
var file = map[byte]byte{
	'a': 0, 'b': 1, 'c': 2, 'd': 3,
	'e': 4, 'f': 5, 'g': 6, 'h': 7}
var files = []byte{'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'}

func mv(f0, r0, f1, r1 byte) { // e4 for now
	y0, x0 := rank[r0], file[f0]
	y1, x1 := rank[r1], file[f1]
	p0 := board[y0][x0]
	p1 := board[y1][x1]
	fmt.Printf("1. %c%c%d", symbol[p0], f0, r0)
	if p1 > 0 { // capture
		fmt.Printf("x")
	}
	fmt.Printf("%c%d\n", f1, r1)
	// TODO: castling
	board[y1][x1] = board[y0][x0]
	board[y0][x0] = 0
}

func show() {
	for _, row := range board {
		for _, x := range row {
			fmt.Printf(" %c", symbol[x])
		}
		fmt.Printf("\n")
	}
}

func main() {
	fmt.Printf("\n")
	fmt.Printf("Opening State\n")
	fmt.Printf("\n")
	show()
	fmt.Printf("\n")
	mv('e', 2, 'e', 4)
	fmt.Printf("\n")
	show()
	fmt.Printf("\n")
}
