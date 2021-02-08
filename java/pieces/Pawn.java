package pieces;

import game.Tile;
import game.Type;
import game.Board;

/**
 * Class representing Pawns.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
 @ invariant this.white != null;
 @ invariant this.moveCount != null && this.moveCount >= 0;
 @ invariant this.type == Type.PAWN;
 @*/
public final class Pawn extends Piece {
	private /*@ non_null */ Integer moveCount;
	
	/**
	 * Constructor using the Piece super-constructor.
	 * @param white Boolean to represent if the piece is white or black
	 */
	/*@
	 @ requires white != null;
	 @ ensures this.white == white && this.type == Type.PAWN && this.moveCount == 0;
	 @ assignable this.white, this.type, this.moveCount;
	 @*/
	public /*@ pure */ Pawn (final /*@ non_null */ boolean white) {
		super(white);
		super.setType(Type.PAWN);
		this.moveCount = 0;
	}
	
	@Override
	/**
	 * Checks if a move is legal or not.
	 * @param board Board to move on
	 * @param start Start-Tile to move from
	 * @param end End-Tile to move to
	 * @return true if the Y-Difference is 2 and its the first move, if the Y-Difference is 1 or if Y-Difference * X-Difference == 1 and it is a taking move; else false.
	 * @ensures returns false if end.getPiece().isWhite() == this.isWhite()
	 * @ensures returns false if !(end.getPiece().isWhite() != this.isWhite() && !this.isWhite() && ((start.getPosition().getPosY() - end.getPosition().getPosY() == 2 && this.moveCount == 0 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (start.getPosition().getPosY() - end.getPosition().getPosY() == 1 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (start.getPosition().getPosY() - end.getPosition().getPosY() * Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 1 && end.getPiece() != null)))
	 * @ensures returns false if !(end.getPiece().isWhite() != this.isWhite() && this.isWhite() && ((end.getPosition().getPosY() - start.getPosition().getPosY() == 2 && this.moveCount == 0 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (end.getPosition().getPosY() - start.getPosition().getPosY() == 1 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (end.getPosition().getPosY() - start.getPosition().getPosY() * Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 1 && end.getPiece() != null)))
	 * @ensures returns true if end.getPiece().isWhite() != this.isWhite() && !this.isWhite() && ((start.getPosition().getPosY() - end.getPosition().getPosY() == 2 && this.moveCount == 0 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (start.getPosition().getPosY() - end.getPosition().getPosY() == 1 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (start.getPosition().getPosY() - end.getPosition().getPosY() * Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 1 && end.getPiece() != null))
	 * @ensures returns true if end.getPiece().isWhite() != this.isWhite() && this.isWhite() && ((end.getPosition().getPosY() - start.getPosition().getPosY() == 2 && this.moveCount == 0 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (end.getPosition().getPosY() - start.getPosition().getPosY() == 1 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (end.getPosition().getPosY() - start.getPosition().getPosY() * Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 1 && end.getPiece() != null))
	 */
	/*@
	 @ ensures end.getPiece().isWhite() == this.isWhite() ==> \result == false;
	 @ ensures end.getPiece().isWhite() != this.isWhite() && this.isWhite() && ((end.getPosition().getPosY() - start.getPosition().getPosY() == 2 && this.moveCount == 0 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (end.getPosition().getPosY() - start.getPosition().getPosY() == 1 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (end.getPosition().getPosY() - start.getPosition().getPosY() * Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 1 && end.getPiece() != null)) ==> \result == true;
	 @ ensures end.getPiece().isWhite() != this.isWhite() && !this.isWhite() && ((start.getPosition().getPosY() - end.getPosition().getPosY() == 2 && this.moveCount == 0 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (start.getPosition().getPosY() - end.getPosition().getPosY() == 1 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (start.getPosition().getPosY() - end.getPosition().getPosY() * Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 1 && end.getPiece() != null)) ==> \result == true;
	 @ ensures !(end.getPiece().isWhite() != this.isWhite() && this.isWhite() && ((end.getPosition().getPosY() - start.getPosition().getPosY() == 2 && this.moveCount == 0 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (end.getPosition().getPosY() - start.getPosition().getPosY() == 1 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (end.getPosition().getPosY() - start.getPosition().getPosY() * Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 1 && end.getPiece() != null))) ==> \result == false;
	 @ ensures !(end.getPiece().isWhite() != this.isWhite() && !this.isWhite() && ((start.getPosition().getPosY() - end.getPosition().getPosY() == 2 && this.moveCount == 0 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (start.getPosition().getPosY() - end.getPosition().getPosY() == 1 && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 0) || (start.getPosition().getPosY() - end.getPosition().getPosY() * Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 1 && end.getPiece() != null))) ==> \result == false;
	 @ assignable x, y;
	 @*/
    public final boolean /*@ pure */ canMove (final /*@ non_null */ Board board, final /*@ non_null */ Tile start, final /*@ non_null */ Tile end) {
        // we can't move the piece to a spot that has 
        // a piece of the same colour 
        if (end.getPiece().isWhite() == this.isWhite()) { 
            return false; 
        };
        
        Integer x = Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX());
        Integer y;
        
        if (this.isWhite()) {
            y = end.getPosition().getPosY() - start.getPosition().getPosY(); 
        } else {
            y = start.getPosition().getPosY() - end.getPosition().getPosY(); 
        };
        
        return (y == 2 && this.moveCount == 0 && x == 0) || (y == 1 && x == 0) || (y * x == 1 && end.getPiece() != null); 
    }
	
	@Override
	/**
	 * Increases the moveCount.
	 */
	/*@
	 @ ensures this.moveCount == \old(this.moveCount) + 1;
	 @ assignable this.moveCount;
	 @*/
	public final /*@ pure */ void increaseMoveCount () {
		this.moveCount++;
	}
}
