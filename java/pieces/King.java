package pieces;

import game.Type;
import game.Tile;
import game.Board;
import game.Position;

/**
 * Class representing Kings.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
 @ invariant this.castled != null;
 @ invariant this.moveCount != null && this.moveCount >= 0;
 @ invariant this.type == Type.KING;
 @ invariant this.white != null;
 @*/
public final class King extends Piece {
	private /*@ non_null */ boolean castled = false;
	private /*@ non_null */ Integer moveCount;
	
	/**
	 * Constructor using the Piece super-constructor.
	 * @param white Boolean to represent if the piece is white or black
	 */
	/*@
	 @ requires white != null;
	 @ ensures this.white == white && this.type == Type.KING && this.moveCount == 0;
	 @ assignable this.white, this.type, this.moveCount;
	 @*/
	public /*@ pure */ King(final /*@ non_null */ boolean white) {
		super(white);
		this.setType(Type.KING);
		this.moveCount = 0;
	}
	
	/**
	 * @return true if castled, false if not
	 */
	/*@
	 @ ensures \result == this.castled;
	 @*/
	public final /*@ pure */ boolean isCastlingDone () { 
        return this.castled; 
    }
	
	/**
	 * Sets the castled attribute.
	 * @param castled the boolean to set it to
	 */
	/*@
	 @ ensures this.castled == castled;
	 @ assignable this.castled;
	 @*/
	public final /*@ pure */ void setCastled (final /*@ non_null */ boolean castled) { 
        this.castled = castled; 
    } 
	
	@Override
	/**
	 * Determines legal moves of the piece.
	 * @param board Board to move on
	 * @param start Start-Tile to move from
	 * @param end End-Tile to move to
	 * @return true if X-Difference + Y-Difference = 1, false if not or if the piece on the end-tile is of the same colour.
	 * @ensures returns false if end.getPiece().isWhite() == this.isWhite()
	 * @ensures returns false if end.getPiece().isWhite() != this.isWhite() && !(Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() + Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 1 || Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() * Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 1)
	 * @ensures returns true if end.getPiece().isWhite() != this.isWhite() && (Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() + Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 1 || Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() * Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 1)
	 */
	/*@
	 @ requires board != null && board instanceof Board;
	 @ requires start != null && start instanceof Tile;
	 @ requires end != null && end instanceof Tile;
	 @ ensures end.getPiece().isWhite() == this.isWhite() ==> \result == false;
	 @ ensures end.getPiece().isWhite() != this.isWhite() && !(Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() + Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 1 || Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() * Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 1 || (Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 2 && Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) == 0)) ==> \result == false;
	 @ ensures end.getPiece().isWhite() != this.isWhite() && (Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() + Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 1 || Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX() * Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY() == 1 || (Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 2 && Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()) == 0)) ==> \result == true;
	 @
	 @ assignable x, y;
	 @*/
    public final boolean canMove (final /*@ non_null */ Board board, final /*@ non_null */ Tile start, final /*@ non_null */ Tile end) { 
        // we can't move the piece to a Spot that  
        // has a piece of the same color 
        if (end.getPiece().isWhite() == this.isWhite()) { 
            return false; 
        };
  
        Integer x = Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()); 
        Integer y = Math.abs(start.getPosition().getPosY() - end.getPosition().getPosY()); 
        if (x + y == 1 || x * y == 1 || (x == 2 && y == 0)) { 
            //TODO check if this move will not result in the king 
            // being attacked if so return true 
            return true; 
        }
  
        return this.isValidCastling(board, start, end); 
    }
	
	/**
	 * Checks if castling is valid.
	 * @param board Board to use
	 * @param start Starting tile of the castling move
	 * @param end End tile of the castling move
	 * @return false if castle is illegal, true if legal
	 * @ensures returns false if this.isCastlingDone() == true
	 * @ensures returns false if this.moveCount != 0
	 */
	/*@
	 @ requires board != null && board instanceof Board;
	 @ requires start != null && start instanceof Tile;
	 @ requires end != null && end instanceof Tile;
	 @ ensures this.isCastlingDone() ==> \result == false;
	 @ ensures this.moveCount != 0 ==> \result == flase;
	 @
	 @*/
	private final boolean isValidCastling (final /*@ non_null */ Board board, final /*@ non_null */ Tile start, final /*@ non_null */ Tile end) { 
		//already castled
		if (this.isCastlingDone()) { 
			return false; 
		}; 
		//already moved King
		if (this.moveCount != 0) {
			return false;
		};
		
		//TODO Checking for check
		
		//not moved Rook
		if (Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 2 && board.getBox(new Position(end.getPosition().getPosX() - 1, end.getPosition().getPosY())).getPiece().getType() == Type.ROOK && board.getBox(new Position(end.getPosition().getPosX() - 1, end.getPosition().getPosY())).getPiece() instanceof Rook && board.getBox(new Position(end.getPosition().getPosX() - 1, end.getPosition().getPosY())).getPiece().getMoveCount() == 0) {
			return true; //short castle
		} else if (Math.abs(start.getPosition().getPosX() - end.getPosition().getPosX()) == 3 && board.getBox(new Position(end.getPosition().getPosX() + 1, end.getPosition().getPosY())).getPiece().getMoveCount() == 0) {
			return true; //long castle
		}
		//default case
		return false;
	}
	
	@Override
	/**
	 * Checks for move.
	 * @param start Starting tile of the castling move
	 * @param end End tile of the castling move
	 * @return true if castling move, false if not
	 */
	/*@
	 @ requires board != null && board instanceof Board;
	 @ requires start != null && start instanceof Tile;
	 @ requires end != null && end instanceof Tile; 
	 @*/
	public final boolean isCastlingMove (final /*@ non_null */ Tile start, final /*@ non_null */ Tile end) { 
        //TODO check if the starting and  
        // ending position are correct 
		return true;
    } 
	
	@Override
	/**
	 * Increases the moveCount.
	 * @ensures this.moveCount = this.moveCount + 1
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
