package pieces;

import game.Tile;
import game.Type;
import game.Board;

/**
 * Class representing Rooks.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
@ invariant this.white != null;
@ invariant this.type == Type.ROOK;
@ invariant this.moveCount >= 0 && this.moveCount != null;
@*/
public final /*@ pure */ class Rook extends Piece {
	private Integer moveCount;
	
	/**
	 * Constructor using the Piece super-constructor.
	 * @param white Boolean to represent if the piece is white or black
	 */
	/*@
	 @ requires white != null;
	 @ ensures this.white == white && this.type == Type.ROOK && this.moveCount == 0;
	 @ assignable this.white, this.type, this.moveCount;
	 @*/
	public /*@ pure */ Rook (final boolean white) {
		super(white);
		super.setType(Type.ROOK);
		this.moveCount = 0;
	}
	
	@Override
	/**
	 * Determines legal moves of the piece.
	 * @param board Board to move on
	 * @param start Start-Tile to move from
	 * @param end End-Tile to move to
	 * @return true if X-Difference is 0 or Y-Difference is 0, false if not or if the piece on the end-tile is of the same colour.s
	 * @ensures returns false if end.getPiece().isWhite() == this.isWhite()
	 * @ensures returns false if end.getPiece().isWhite() != this.isWhite() && !(Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) + Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) || Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()))
	 * @ensures returns true if end.getPiece().isWhite() != this.isWhite() && (Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) + Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) || Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()))
	 */
	/*@
	 @ requires board != null && board instanceof Board;
	 @ requires start != null && start instanceof Tile;
	 @ requires end != null && end instanceof Tile;
	 @ ensures end.getPiece().isWhite() == this.isWhite() ==> \result == false;
	 @ ensures end.getPiece().isWhite() != this.isWhite() && !(Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) + Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) || Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX())) ==> \result == false;
	 @ ensures end.getPiece().isWhite() != this.isWhite() && (Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) + Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) || Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) == Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) + Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX())) ==> \result == true;
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
        
        return x == x+y || y == x+y; 
    }
	
	@Override
	/**
	 * Increases the moveCount.
	 * @ensures this.moveCount == this.moveCount + 1
	 */
	/*@
	 @ ensures this.moveCount == \old(this.moveCount) + 1;
	 @ assignable this.moveCount;
	 @*/
	public final /*@ pure */ void increaseMoveCount () {
		this.moveCount++;
	}

	@Override
	/**
	 * @return moveCount
	 */
	/*@
	 @ ensures \result == this.moveCount;
	 @*/
	public final /*@ pure */ Integer getMoveCount () {
		return this.moveCount;
	}
}
