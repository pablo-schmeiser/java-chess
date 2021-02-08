package pieces;

import game.Type;
import game.Tile;
import game.Board;

/**
 * Abstract-Class representing Pieces.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
 @ invariant type != null && type instanceof Type;
 @ invariant taken != null && (taken || !taken);
 @ invariant white != null && (white || !white);
 @*/
public abstract class Piece {
	private Type type;
	private /*@ non_null */ boolean taken = false;
	private /*@ non_null */ final boolean white;
	
	/**
	 * @param white Boolean object representing if it is white
	 * @ensures this.white == white
	 */
	/*@
	 @ requires white != null && (white || !white);
	 @ ensures this.white == white;
	 @ assignable this.white;
	 @*/
	public /*@ pure */ Piece (final /*@ non_null */ boolean white) {
		this.white = white;
	}
	
	/**
	 * Gets if the piece is white or black.
	 * @return true if piece is white, false if piece is black
	 */
	/*@
	 @ ensures \result == this.white;
	 @*/
	public final /*@ pure */ boolean isWhite () { 
        return this.white; 
    }
	
	/**
	 * Gets if the piece is taken or not.
	 * @return true if piece is taken, false if not
	 */
	/*@
	 @ ensures \result == this.taken;
	 @*/
	public final /*@ pure */ boolean isTaken () { 
        return this.taken; 
    }
	
	/**
	 * @param taken Boolean object representing if it is taken
	 */
	/*@
	 @ ensures this.taken == taken;
	 @ assignable this.taken;
	 @*/
	public final /*@ pure */ void setTaken (final /*@ non_null */ boolean taken) { 
        this.taken = taken; 
    }
	
	/**
	 * Determines legal moves of the piece.
	 * @param board Board to move on
	 * @param start Start-Tile to move from
	 * @param end End-Tile to move to
	 * @return true if move is legal, false if not
	 * @ensures returns a boolean
	 */
	/*@
	 @ requires board != null && board instanceof Board;
	 @ requires start != null && start instanceof Tile;
	 @ requires end != null && end instanceof Tile;
	 @*/
	/*@
	 @ ensures \result || !(\result);
	 @*/
	public abstract /*@ pure */ boolean canMove (final /*@ non_null */ Board board, final /*@ non_null */ Tile start, final /*@ non_null */ Tile end);
	
	/**
	 * Placeholder so isCastlingMove can be executed on Pieces and not only on Kings. 
	 * @return false
	 */
	/*@
	 @ ensures \result == false;
	 @*/
	public /*@ pure */ boolean isCastlingMove () {
		return false;
	}
	
	/**
	 * @return type of the piece
	 */
	/*@
	 @ ensures \result == this.type; 
	 @*/
	public final Type getType () {
		return this.type;
	}
	
	/**
	 * @param type Type to set to
	 */
	/*@
	 @ requires type != null && type instanceof Type;
	 @ ensures this.type == type;
	 @*/
	public final /*@ pure */ void setType (final /*@ non_null */ Type type) {
		this.type = type;
	}
	
	/**
	 * Placeholder so increaseMoveCount can be executed on Pieces and not only on Kings, Pawns and Rooks.
	 */
	public /*@pure */ void increaseMoveCount () {}
	
	/**
	 * Placeholder so isCastlingMove can be executed on Pieces and not only on Kings.
	 * @param start Starting tile of the castling move
	 * @param end End tile of the castling move
	 * @return true if castling move, false if not
	 */
	public /*@pure */ boolean isCastlingMove (final /*@ non_null */ Tile start, final /*@ non_null */ Tile end) {
		return false;
	}
	
	/**
	 * Placeholder so getMoveCount can be executed on Pieces and not only on Kings, Pawns and Rooks.
	 * @return 1
	 */
	public /*@pure */ Integer getMoveCount () {
		return 1;
	}
}
