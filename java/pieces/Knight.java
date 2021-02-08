package pieces;

import game.Board;
import game.Tile;
import game.Type;

/**
 * Class representing Knights.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
@ invariant this.white != null;
@ invariant this.type == Type.KNIGHT;
@*/
public final /*@ pure */ class Knight extends Piece {
	
	/**
	 * Constructor using the Piece super-constructor.
	 * @param white Boolean to represent if the piece is white or black
	 */
	/*@
	 @ requires white != null;
	 @ ensures this.white == white && this.type == Type.KNIGHT;
	 @ assignable this.white, this.type;
	 @*/
	public /*@ pure */ Knight (final /*@ non_null */ boolean white) { 
        super(white);
        super.setType(Type.KNIGHT);
    } 
  
    @Override
    /**
     * Determines legal moves of the piece.
     * @param board Board to move on
	 * @param start Start-Tile to move from
	 * @param end End-Tile to move to
	 * @return true if X-Difference * Y-Difference = 2, false if not or if the piece on the end-tile is of the same colour.
	 * @ensures returns false if end.getPiece().isWhite() == this.isWhite()
	 * @ensures returns false if end.getPiece().isWhite() != this.isWhite() && !(Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() * Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 2)
	 * @ensures returns true if end.getPiece().isWhite() != this.isWhite() && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() * Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 2
     */
    /*@
     @ requires board != null && board instanceof Board;
	 @ requires start != null && start instanceof Tile;
	 @ requires end != null && end instanceof Tile;
	 @ ensures end.getPiece().isWhite() == this.isWhite() ==> \result == false;
	 @ ensures end.getPiece().isWhite() != this.isWhite() && !(Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() * Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 2) ==> \result == false;
     @ ensures end.getPiece().isWhite() != this.isWhite() && Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() * Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 2 ==> \result == true;
     @ assignable x, y;
     @*/
    public final boolean /*@ pure */ canMove (final /*@ non_null */ Board board, final /*@ non_null */ Tile start, final /*@ non_null */ Tile end) { 
        // we can't move the piece to a spot that has 
        // a piece of the same colour 
        if (end.getPiece().isWhite() == this.isWhite()) { 
            return false; 
        };
  
        Integer x = Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()); 
        Integer y = Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()); 
        return x * y == 2; 
    }
}
