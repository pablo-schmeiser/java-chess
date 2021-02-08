package game;

import pieces.*;

/**
 * Class representing chessboards.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
 @ invariant this.boxes != null && this.boxes instanceof Tile[][];
 @*/
public final /*@ pure */ class Board {
	private /*@ non_null; */ Tile[][] boxes;
	
	/**
	 * Creates a new chessboard.
	 */
	public /*@ pure */ Board() {
		this.resetBoard();
	}
	
	/**
	 * Returns the tile on a chessboard at a certain position.
	 * @param position Position to get the box from
	 * @return tile at [x][y]
	 * @ensures this.boxes[position.getPosX()][position.getPosY()]
	 */
	/*@
	 @ requires position != null && position instanceof Position && position.getPosX() != null && position.getPosY() != null;
	 @ ensures \result == this.boxes[position.getPosX()][position.getPosY()];
	 @*/
	public final /*@ pure */ Tile getBox (final Position position) {
		return this.boxes[position.getPosX()][position.getPosY()];
	}
	
	/**
	 * Resets the board into the position of the normal chessboard startformation.
	 * @ensures positions starting pieces in the standard chess starting position
	 */
	/*@
	 @ ensures \forall Integer 0 <= i <= 8; this.boxes[i][1].equals(new Position(i, 1), new Pawn(true));
	 @ ensures \forall Integer 0 <= i <= 8; this.boxes[i][6].equals(new Position(i, 6), new Pawn(false));
	 @ ensures this.boxes[0][0].equals(new Tile(new Position(0, 0), new Rook(true))) && this.boxes[7][0].equals(new Tile(new Position(7, 0), new Rook(true)));
	 @ ensures this.boxes[0][7].equals(new Tile(new Position(0, 7), new Rook(false))) && this.boxes[7][7].equals(new Tile(new Position(7, 7), new Rook(false)));
	 @ ensures this.boxes[1][0].equals(new Tile(new Position(1, 0), new Knight(true))) && this.boxes[6][0].equals(new Tile(new Position(6, 0), new Knight(true)));
	 @ ensures this.boxes[1][7].equals(new Tile(new Position(1, 7), new Knight(false))) && this.boxes[6][7].equals(new Tile(new Position(6, 7), new Knight(false)));
	 @ ensures this.boxes[2][0].equals(new Tile(new Position(2, 0), new Bishop(true))) && this.boxes[5][0].equals(new Tile(new Position(5, 0), new Bishop(true)));
	 @ ensures this.boxes[2][7].equals(new Tile(new Position(2, 7), new Bishop(false))) && this.boxes[5][7].equals(new Tile(new Position(5, 7), new Bishop(false)));
	 @ ensures this.boxes[3][0].equals(new Tile(new Position(3, 0), new Queen(true))) && this.boxes[4][0].equals(new Tile(new Position(4, 0), new King(true)));
	 @ ensures this.boxes[3][7].equals(new Tile(new Position(3, 7), new Queen(false))) && this.boxes[4][7].equals(new Tile(new Position(4, 7), new King(false)));
	 @ ensures \forall Integer 0 <= i <= 8, 2 <= j <= 6; this.boxes[i][j].equals(new Tile(new Position(i, j), null);
	 @ assignable this.boxes;
	 @*/
	public final /*@ pure */ void resetBoard () {
		/*@
		 @ loop_invariant (\forall Integer j; j >= 0 && j < 8);
		 @*/
		for (Integer j = 0; j < 8; j = j + 7) {
			boolean white = true;
			if (j != 0) {
				white = false;
			};
			/*@
			 @ loop_invariant (\forall Integer i; i >= 0 && i < 8);
			 @*/
			for (Integer i = 0; i < 8; i++) {
				Integer side = 1;
				if (j != 0) {
					side = -1;
				};
				this.boxes[i][j + side] = new Tile(new Position(i, j + side), new Pawn(white));
			};
			this.boxes[0][j] = new Tile(new Position(0, j), new Rook(white));
			this.boxes[1][j] = new Tile(new Position(1, j), new Knight(white));
			this.boxes[2][j] = new Tile(new Position(2, j), new Bishop(white));
        	this.boxes[3][j] = new Tile(new Position(3, j), new Queen(white));
        	this.boxes[4][j] = new Tile(new Position(4, j), new King(white));
        	this.boxes[5][j] = new Tile(new Position(5, j), new Bishop(white));
        	this.boxes[6][j] = new Tile(new Position(6, j), new Knight(white));
        	this.boxes[7][j] = new Tile(new Position(7, j), new Rook(white));
		};
		/*@
		 @ loop_invariant (\forall Integer j; j >= 0 && j < 8);
		 @*/
		for (Integer j = 0; j < 8; j++) {
			/*@
			 @ loop_invariant (\forall Integer i; i >= 2 && i < 6);
			 @*/
			for (Integer i = 2; i < 7; i++) {
				this.boxes[j][i] = new Tile(new Position(j, i), null);
			}
		}
	}
	
}
