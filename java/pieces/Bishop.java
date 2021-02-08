package pieces;

import game.Type;
import game.Tile;
import game.Board;

/**
 * Class representing Bishops.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
 @ invariant this.white != null;
 @ invariant this.type == Type.BISHOP;
 @*/
public final /*@ pure */ class Bishop extends Piece {
	/**
	 * Constructor using the Piece super-constructor.
	 * @param white Boolean to represent if the piece is white or black
	 */
	/*@
	 @ requires white != null;
	 @ ensures this.white == white && this.type == Type.BISHOP;
	 @ assignable this.white, this.type;
	 @*/
	public /*@ pure */ Bishop (final /*@ non_null */ boolean white) {
		super(white);
		super.setType(Type.BISHOP);
	}
	
	@Override
	/**
	 * Determines legal moves of the piece.
	 * @param board Board to move on
	 * @param start Start-Tile to move from
	 * @param end End-Tile to move to
	 * @return true if X-Difference and Y-Difference are equal, false if not or if the piece on the end-tile is of the same colour.
	 * @ensures returns false if end.getPiece().isWhite() == this.isWhite()
	 * @ensures returns false if !(Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY())) && end.getPiece().isWhite() != this.isWhite()
	 * @ensures returns true if end.getPiece().isWhite() != this.isWhite() && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY())
	 */
	/*@
	 @ requires board != null && board instanceof Board;
	 @ requires start != null && start instanceof Tile;
	 @ requires end != null && end instanceof Tile;
	 @ ensures end.getPiece().isWhite() == this.isWhite() ==> \result == false;
	 @ ensures end.getPiece().isWhite() != this.isWhite() && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) ==> \result == true;
	 @ ensures !(Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY())) && end.getPiece().isWhite() != this.isWhite() ==> false;
	 @ assignable x, y;
	 @*/
    public final /*@ pure */ boolean canMove(final /*@ non_null */ Board board, final /*@ non_null */ Tile start, final /*@ non_null */ Tile end) { 
        // we can't move the piece to a spot that has 
        // a piece of the same colour 
        if (end.getPiece().isWhite() == this.isWhite()) { 
            return false; 
        };
  
        Integer x = Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()); 
        Integer y = Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()); 
        
        return x == y; 
    }

}
