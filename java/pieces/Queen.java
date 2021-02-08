package pieces;

import game.Tile;
import game.Type;
import game.Board;

/**
 * Class representing Queens.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
 @ invariant this.white != null;
 @ invariant this.type == Type.QUEEN;
 @*/
public final /*@ pure */ class Queen extends Piece {

	/**
	 * Constructor using the Piece super-constructor.
	 * @param white Boolean to represent if the piece is white or black
	 */
	/*@
	 @ requires white != null;
	 @ ensures this.white == white && this.type == Type.QUUEN;
	 @ assignable this.white, this.type;
	 @*/
	public /*@ pure */ Queen (final boolean white) {
		super(white);
		super.setType(Type.QUEEN);
	}
	
	@Override
	/**
	 * Determines legal moves of the piece.
	 * @param board Board to move on
	 * @param start Start-Tile to move from
	 * @param end End-Tile to move to
	 * @return true if X-Difference and Y-Difference are equal, X-Difference is 0 or Y-Difference is 0, false if not or if the piece on the end-tile is of the same colour.
	 * @ensures returns false if end.getPiece().isWhite() == this.isWhite()
	 * @ensures returns false if (end.getPiece().isWhite() != this.isWhite() && !(Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() || Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) || Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX())))
	 * @ensures returns true if (end.getPiece().isWhite() != this.isWhite() && (Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() || Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) || Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX())))
	 */
	/*@
	 @ requires board != null && board instanceof Board;
	 @ requires start != null && start instanceof Tile;
	 @ requires end != null && end instanceof Tile;
	 @ ensures end.getPiece().isWhite() == this.isWhite() ==> \result == false;
	 @ ensures end.getPiece().isWhite() != this.isWhite() && (Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() || Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) || Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX())) ==> \result == true;
	 @ ensures end.getPiece().isWhite() != this.isWhite() && !(Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() || Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) || Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX())) ==> \result == false;
	 @ assignable x, y;
	 @*/
    public final /*@ pure */ boolean canMove(final Board board, final Tile start, final Tile end) { 
        // we can't move the piece to a spot that has 
        // a piece of the same colour 
        if (end.getPiece().isWhite() == this.isWhite()) { 
            return false; 
        };
  
        Integer x = Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()); 
        Integer y = Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()); 
        
        return x == y || x == x+y || y == x+y; 
    }
	
}
