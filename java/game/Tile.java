package game;

import pieces.Piece;

/**
 * Class representing a Tile on a chessboard.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
 @ invariant this.position != null && !(this.position instanceof Position);
 @*/
public final /*@ pure */ class Tile {
	private Piece piece;
	private final /*@ non_null */ Position position;
	
	/**
	 * @throws NullPointerException Position may not be null.
	 * @param position Position to set the position attribute to
	 * @param piece Piece to set the piece attribute to
	 * @ensures this.piece == piece && this.position == position
	 */
	/*@
	 @ ensures this.piece == piece && this.position == position;
	 @ signals (NullPointerException e) position == null;
	 @ assignable this.piece, this.position;
	 @*/
	public /*@ pure */ Tile (final Position position, final Piece piece) {
		if (position == null) {
			throw new NullPointerException("Position may not be null.");
		};
		this.setPiece(piece);
		this.position = position;
	}
	
	/**
	 * Sets the piece of the tile Object.
	 * @param piece Piece to set the piece attribute to
	 * @ensures this.piece == piece
	 */
	/*@
	 @ ensures this.piece == piece;
	 @ assignable this.piece;
	 @*/
	public final /*@ pure */ void setPiece (final Piece piece) {
		this.piece = piece;
	}
	
	/**
	 * @return piece standing on the tile (if null - no piece on tile)
	 * @ensures returns this.piece
	 */
	/*@
	 @ ensures \result == this.piece;
	 @*/
	public final /*@ pure */ Piece getPiece () { 
        return this.piece; 
    }
	
	/**
	 * @return position of the tile
	 * @ensures returns this.position
	 */
	/*@
	 @ ensures \result == this.position;
	 @*/
	public final /*@ pure */ Position getPosition () { 
        return this.position; 
    }

}
