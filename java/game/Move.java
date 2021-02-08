package game;

import pieces.Piece;
import players.Player;

/**
 * Class representing a chess move.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
 @ invariant this.player != null && !(this.player instanceof Player);
 @ invariant this.start != null && !(this.start instanceof Tile);
 @ invariant this.end != null && !(this.end instanceof Tile);
 @ invariant this.pieceMoved != null && !(this.pieceMoved instanceof Piece);
 @ invariant this.castlingMove != null;
 @*/
public /*@ pure */ class Move {
	private final /*@ non_null */ Player player;
	private final /*@ non_null */ Tile start;
	private final /*@ non_null */ Tile end;
	private final /*@ non_null */ Piece pieceMoved;
	private Piece pieceTaken;
	private /*@ non_null */ boolean castlingMove = false;
	
	/**
	 * @throws NullPointerException Player, start tile and end tile may not be null.
	 * @throws IllegalArgumentException Player, start tile or end tile have to be the right type.
	 * @param player Player to set the player attribute to
	 * @param start Tile to set the start attribute to
	 * @param end Tile to set the end attribute to
	 * @ensures this.player == player && this.start == start && this.end == end && this.pieceMoved == start.getPiece()
	 */
	/*@
	 @ ensures this.player == player && this.start == start && this.end == end && pieceMoved == start.getPiece();
	 @ signals (NullPointerException e) player == null || start == null || end == null || start.getPiece() == null;
	 @ signals (IllegalArgumentException e2) !(player instanceof Player && start instanceof Tile && end instanceof Tile && start.getPiece() instanceof Piece);
	 @ assignable this.player, this.start, this.end, this.pieceMoved;
	 @*/
	public /*@ pure */ Move (final Player player, final Tile start, final Tile end) {
		if (player == null || start == null || end == null || start.getPiece() == null) {
			throw new NullPointerException("Player, start tile and end tile may not be null.");
		};
		if (!(player instanceof Player && start instanceof Tile && end instanceof Tile && start.getPiece() instanceof Piece)) {
			throw new IllegalArgumentException("Player, start tile or end tile have to be the right type.");
		};
		this.player = player;
		this.start = start;
		this.end = end;
		this.pieceMoved = start.getPiece();
	}
	
	/**
	 * @return true if castling move, false if not
	 * @ensures returns this.castlingMove
	 */
	/*@
	 @ ensures \result == this.castlingMove;
	 @*/
	public final /*@ pure */ boolean isCastlingMove () { 
        return this.castlingMove;
    } 
	
	/**
	 * @param castlingMove Boolean representing if king was castled this turn
	 * @ensures this.castlingMove == castlingMove
	 */
	/*@
	 @ requires castlingMove != null;
	 @ ensures this.castlingMove == castlingMove;
	 @ assignable this.castlingMove;
	 @*/
    public final /*@ pure */ void setCastlingMove (final boolean castlingMove) { 
        this.castlingMove = castlingMove;
    }
    
    /**
     * @return Tile the piece is moved from
     * @ensures returns this.start
     */
    /*@
     @ ensures \result == this.start;
     @*/
    public final /*@ pure */ Tile getStart () {
    	return this.start;
    }
    
    /**
     * @return Tile the piece is moved to
     * @ensures returns this.end
     */
    /*@
     @ ensures \result == this.end;
     @*/
    public final /*@ pure */ Tile getEnd () {
    	return this.end;
    }
    
    /**
     * @param piece taken piece
     * @ensures this.pieceTaken == piece
     */
    /*@
     @ requires piece != null && piece instanceof Piece;
     @ ensures this.pieceTaken == piece;
     @ assignable this.pieceTaken;
     @*/
    public final /*@ pure */ void setPieceTaken (final Piece piece) {
    	this.pieceTaken = piece;
    }
    
    /**
     * @return taken piece
     * @ensures returns this.pieceTaken
     */
    /*@
     @ ensures \result == this.pieceTaken;
     @*/
    public final /*@ pure */ Piece getPieceTaken () {
    	return this.pieceTaken;
    }
    
    /**
     * @return the player who made the move
     * @ensures returns this.player
     */
    /*@
     @ ensures \result == this.player;
     @*/
    public final /*@ pure */ Player getPlayer () {
    	return this.player;
    }
    
    /**
     * @return moved piece
     * @ensures returns this.pieceMoved
     */
    /*@
     @ ensures \result == this.pieceMoved;
     @*/
    public final /*@ pure */ Piece getPieceMoved () {
    	return this.pieceMoved;
    }

}
