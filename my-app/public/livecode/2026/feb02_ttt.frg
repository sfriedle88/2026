#lang forge/froglet

/*
  I'd love to use the new CnD visualization support for Feb 02's model. 
  The trouble is: these visualizations expect any atom to only appear
  _once_. So the way I wrote this model isn't super good for CnD. 

  That said, beware making modeling choices _just_ for nice visualizations.
  Often it's fine and helpful, but double-check to make sure you're not 
  making your life harder down the road. 

  Here's an example. To make a good visualization, I've changed the entire
  data model so that there's an atom for every cell in the board. Now I 
  need to decide where the state changes live: do player marks belong as 
  fields of a cell, or as a partial-function in Board as before? 

  If I make marks a field of Cell, I need to instantiate 9 cells for 
  every board! 2*9 = 18 for a single step, up to 10*9 = 90 for a full
  game. More atoms often means more scaling problems.

  So instead, let's keep the same 9 cells for every board. 
*/

/*
ASSUMPTIONS:
- Assuming that the board is only a 3x3
*/

abstract sig Player {} 
one sig X, O extends Player {}

/** Cells are fixed indexes. We'll need to constrain their rows and 
    columns in our well-formed predicate. */
sig Cell {
    row: one Int,
    col: one Int
}

/** Player moves vary by board state; use the same */
sig Board {
    board: pfunc Cell -> Player
}

/** This is no longer about single boards, but about our collection
    of static cell atoms. */
pred wellformed {
    all c: Cell | {
        c.row >= 0 
        c.row <= 2 
        c.col >= 0 
        c.col <= 2
    }
    all disj c1,c2: Cell | {
        (c1.row != c2.row) or
        (c1.col != c2.col)
    }
}

/** This board is a starting state for the game. */
pred starting[b: Board] {
  all c: Cell | {
    no b.board[c]
  }
}


pred winRow[b: Board, p: Player] {
    /*some row: Int | {
        b.board[row][0] = p
        b.board[row][1] = p
        b.board[row][2] = p
    }*/
    // Three in a row
    some c1, c2, c3: Cell | {
        b.board[c1] = p
        b.board[c2] = p
        b.board[c3] = p
        c1.row = c2.row
        c2.row = c3.row
    }
}

pred winCol[b: Board, p: Player] {
    some c1, c2, c3: Cell | {
        b.board[c1] = p
        b.board[c2] = p
        b.board[c3] = p
        c1.col = c2.col
        c2.col = c3.col
    }
}

pred winDiag[b: Board, p: Player] {
    some c1, c2, c3: Cell | {
        b.board[c1] = p
        b.board[c2] = p
        b.board[c3] = p
        // Notice my defensive parens here. I can't _remember_ the order
        // of operations, and it might be fine, but I want to protect myself 
        // against this being interpreted as (A and B) or C, instead of 
        // A and (B or C).
        ({
            c1.row = 0
            c1.col = 0
            c2.row = 1
            c2.col = 1
            c3.row = 2
            c3.col = 2
        } or {
            c1.row = 0
            c1.col = 2
            c2.row = 1
            c2.col = 1
            c3.row = 2
            c3.col = 0
        })
    }
    // { 
    //   b.board[0][0] = p  
    //   b.board[1][1] = p
    //   b.board[2][2] = p
    // } or { 
    //   b.board[0][2] = p  
    //   b.board[1][1] = p
    //   b.board[2][0] = p
    // }
}

pred winning[b: Board, p: Player] {
    winRow[b, p] or 
    winCol[b, p] or 
    winDiag[b, p]
}

/** It's X's turn in this board */
pred Xturn[b: Board] {
    #{c : Cell | b.board[c] = X}
    = 
    #{c : Cell | b.board[c] = O}
//   #{row, col: Int | b.board[row][col] = X}
//   = 
//   #{row, col: Int | b.board[row][col] = O}
}

/** It's O's turn in this board */
pred Oturn[b: Board] {
  -- NO: not XTurn[b]
    #{c : Cell | b.board[c] = X}
    = 
    add[1, #{c : Cell | b.board[c] = O}]

//   #{row, col: Int | b.board[row][col] = X}
//   = 
//   add[#{row, col: Int | b.board[row][col] = O}, 1]
}

/** Potentially-reachable board state */
pred balanced[b: Board] {
    Xturn[b] or Oturn[b]
}

// I rewrote this. But notice how I needed to allow >4 Cells!
cell_board: run { 
    wellformed
    // Could also do #Cell = 9 instead of "exactly 9 cell" at the bottom
      // What could be the disadvantage of this? -> look into this 
    some b: Board | {
        balanced[b]
        winning[b, X]
    }
} for exactly 1 Board, exactly 9 Cell
// 

/** State transition from pre to post, 
    as <p> makes a move at <row>,<col> 
     
    NOTE: please don't use a field name as a variable name...
    */
-- pred move[pre: Board, row: Int, col: Int, p: Player, post: Board] {
pred move[pre: Board, moveRow: Int, moveCol: Int, p: Player, post: Board] {
  -- GUARD
  --   It's the player's turn to move 
  p = X implies Xturn[pre]
  p = O implies Oturn[pre]
  
  --   There is no mark in row,col yet
  -- Note: we have to be more verbose here. We have better language later on.
  all c: Cell | (c.row = moveRow and c.col = moveCol) implies {
    no pre.board[c]
  }
  -- no pre.board[row][col]

  --   The game is not over (nobody has won)
  --not winning[pre, X] 
  --not winning[pre, O]
    -- ? where do we check for this?
  --   Row/col should be within the valid spaces
  moveRow >= 0 and moveRow <= 2
  moveCol >= 0 and moveCol <= 2
  -- ACTION
  --   Next player's turn after
  --     (What do we need to do here?)
  --   Mark for player p is now in row,col
  all c: Cell | (c.row = moveRow and c.col = moveCol) implies {
    post.board[c] = p
    -- Note how tempting it is to merge the guard + action here
  }
  -- post.board[row][col] = p

  --   "Frame Condition": everything ELSE is the same
  all c: Cell| (c.row != moveRow or c.col != moveCol) implies {
    post.board[c] = pre.board[c]
  }
}

cells_step: run { 
    wellformed
    some b1, b2: Board | {
        balanced[b1]
        some r,c: Int, p: Player | 
          move[b1, r, c, p, b2]
    }
} for exactly 2 Board, exactly 9 Cell
