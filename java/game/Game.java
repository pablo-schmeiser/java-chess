package game;

import pieces.Piece;
import players.Player;
import pieces.King;
import java.util.Stack;

/**
 * Class representing a game of chess.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
 @ invariant this.players != null && this.players instanceof Players;
 @ invariant this.board != null && this.board instanceof Board;
 @ invariant this.currentTurn != null && this.currentTurn instanceof Player;
 @ invariant this.status != null && this.status instanceof GameStatus;
 @ invariant this.movesPlayed != null && this.movesPlayed instanceof Stack<Move>;
 @*/
public final class Game {
	private /*@ non_null */ Player[] players; 
    private /*@ non_null */ Board board; 
    private /*@ non_null */ Player currentTurn; 
    private /*@ non_null */ GameStatus status; 
    private /*@ non_null */ Stack<Move> movesPlayed; 
	
    /**
     * Initializes the Game using {@link initialize}.
     * @throws NullPointerException Players may not be null.
     * @param p1 Player 1
     * @param p2 Player 2
     */
    /*@
     @ requires p1 instanceof Player && p2 instanceof Player;
     @ signals (NullPointerException e) p1 == null || p2 == null;
     @*/
    public /*@ pure */ Game (final Player p1, final Player p2) {
    	if (p1 == null || p2 == null) {
    		throw new NullPointerException("Players may not be null.");
    	};
    	this.initialize(p1, p2);
    }
    
    /**
     * Initializes the game with 2 players, resets the board, clears the movesPlayed log and sets a beginner.
     * @throws NullPointerException Players may not be null.
     * @param p1 Player 1
     * @param p2 Player 2
     * @ensures this.players[0] == p1 && this.players[1] == p2 && this.board.equals(new Board()) && this.movesPlayed.equals(new Stack<Move>()) && this.status == GameStatus.ACTIVE
     * @ensures p1.isWhiteSide() ==> this.currentTurn == p1
     * @ensures !p1.isWhiteSide() ==> this.currentTurn == p2
     */
    /*@
     @ signals (NullPointerException e) p1 == null && || p2 == null;
     @ ensures this.players[0] == p1 && this.players[1] == p2 && this.board.equals(new Board()) && this.movesPlayed.equals(new Stack<Move>()) && this.status == GameStatus.ACTIVE;
     @ ensures p1.isWhiteSide() ==> this.currentTurn == p1;
     @ ensures !p1.isWhiteSide() ==> this.currentTurn == p2;
     @ assignable this.player, this.board, this.currentTurn, this.movesPlayed, this.status;
     @*/
    private final /*@ pure */ void initialize (final Player p1, final Player p2) { 
    	if (p1 == null || p2 == null) {
    		throw new NullPointerException("Players may not be null.");
    	};
    	
        this.players[0] = p1; 
        this.players[1] = p2; 
  
        this.board = new Board(); 
  
        if (p1.isWhiteSide()) { 
            this.currentTurn = p1; 
        } else { 
            this.currentTurn = p2; 
        };
  
        this.movesPlayed = new Stack<Move>(); 
        this.status = GameStatus.ACTIVE;
    } 
  
    /**
     * @return true if game ended, false if not
     * @ensures \result == (this.getStatus() != GameStatus.ACTIVE)
     * @ensures (this.getStatus() != GameStatus.ACTIVE) ==> \result == true
     * @ensures !(this.getStatus() != GameStatus.ACTIVE) ==> \result == false
     */
    /*@
     @ ensures \result == (this.getStatus() != GameStatus.ACTIVE);
     @ ensures (this.getStatus() != GameStatus.ACTIVE) ==> \result == true;
     @ ensures !(this.getStatus() != GameStatus.ACTIVE) ==> \result == false;
     @*/
    public final boolean isEnd () { 
        return this.getStatus() != GameStatus.ACTIVE; 
    } 
    
    /**
     * @return status of the game
     * @ensures returns this.status
     */
    /*@
     @ ensures \result == this.status;
     @*/
    public final GameStatus getStatus () { 
        return this.status; 
    } 
    
    /**
     * Sets the games status to a given status.
     * @param status status to set to
     * @ensures this.status == status
     */
    /*@
     @ requires status != null && status instanceof GameStatus;
     @ ensures this.status == status;
     @ assignable this.status;
     @*/
    public final /*@ pure */ void setStatus (final GameStatus status) { 
        this.status = status; 
    } 
    
    /**
     * Creates a move for a player and makes the move using {@link makeMove}.
     * @param player Player the piece belongs to
     * @param startPosition Position the move started at
     * @param endPosition Position the move ends at
     * @return true if the move was succesfull, else not
     */
    /*@
     @ requires player != null && player instanceof Player;
     @ requires startPosition != null && startPosition instanceof Position && startPosition.getPosX() != null && startPosition.getPosX() >= 0 && startPosition.getPosX() <= 7 && startPosition.getPosY() != null && startPosition.getPosY() >= 0 && startPosition.getPosY() <= 7;
     @ requires endPosition != null && endPosition instanceof Position && endPosition.getPosX() != null && endPosition.getPosX() >= 0 && endPosition.getPosX() <= 7 && endPosition.getPosY() != null && endPosition.getPosY() >= 0 && endPosition.getPosY() <= 7;
     @ assignable move, startBox, endBox, destPiece, this.status, this.currentTurn;
     @*/
    public final boolean playerMove (final Player player, final Position startPosition, final Position endPosition) { 
        Tile startBox = board.getBox(startPosition); 
        Tile endBox = board.getBox(endPosition); 
        Move move = new Move(player, startBox, endBox); 
        return this.makeMove(move, player); 
    } 
  
    /**
     * Makes a move.
     * @param move Move to make
     * @param player Player making the move
     * @return true if the move was succesfull, else not
     * @ensures returns false if move.getStart().getPiece() == null
     * @ensures returns false if move.player != currentTurn
     * @ensures returns false if sourcePiece.isWhite() != player.isWhiteSide()
     * @ensures returns false if !sourcePiece.canMove(board, move.getStart(), move.getEnd())
     * @ensures returns true if !(move.getStart().getPiece() == null) && !(move.player != currentTurn) && !(sourcePiece.isWhite() != player.isWhiteSide()) && sourcePiece.canMove(board, move.getStart(), move.getEnd())
     * @ensures sets status to WHITE_WIN if destPiece != null && destPiece instanceof King && player.isWhiteSide()
     * @ensures sets status to BLACK_WIN if destPiece != null && destPiece instanceof King && !(player.isWhiteSide())
     * @ensures changes currentTurn to the other player
     */
    /*@
     @ requires move != null && move instanceof Move;
     @ requires player != null && player instanceof Player;
     @ ensures (move.getStart().getPiece() == null) ==> \result == false;
     @ ensures (move.player != currentTurn) ==> \result == false;
     @ ensures (sourcePiece.isWhite() != player.isWhiteSide()) ==> \result == false;
     @ ensures (!sourcePiece.canMove(board, move.getStart(), move.getEnd())) ==> \result == false;
     @ ensures !(move.getStart().getPiece() == null) && !(move.player != currentTurn) && !(sourcePiece.isWhite() != player.isWhiteSide()) && sourcePiece.canMove(board, move.getStart(), move.getEnd()) ==> \result == true;
     @ ensures (destPiece != null && destPiece instanceof King && player.isWhiteSide() && !(move.getStart().getPiece() == null) && !(move.player != currentTurn) && !(sourcePiece.isWhite() != player.isWhiteSide()) && sourcePiece.canMove(board, move.getStart(), move.getEnd())) ==> this.status == GameStatus.WHITE_WIN;
     @ ensures (destPiece != null && destPiece instanceof King && !(player.isWhiteSide()) && !(move.getStart().getPiece() == null) && !(move.player != currentTurn) && !(sourcePiece.isWhite() != player.isWhiteSide()) && sourcePiece.canMove(board, move.getStart(), move.getEnd())) ==> this.status == GameStatus.BLACK_WIN;
     @ ensures (this.currentTurn == players[0] && !(move.getStart().getPiece() == null) && !(move.player != currentTurn) && !(sourcePiece.isWhite() != player.isWhiteSide()) && sourcePiece.canMove(board, move.getStart(), move.getEnd())) ==> this.currentTurn = players[1];
     @ ensures (this.currentTurn == players[1] && !(move.getStart().getPiece() == null) && !(move.player != currentTurn) && !(sourcePiece.isWhite() != player.isWhiteSide()) && sourcePiece.canMove(board, move.getStart(), move.getEnd())) ==> this.currentTurn = players[0];
     @ assignable move, destPiece, sourcePiece, this.status, this.currentTurn;
     @*/
    private final boolean makeMove (final Move move, final Player player) { 
        Piece sourcePiece = move.getStart().getPiece(); 
        if (sourcePiece == null) { 
            return false; 
        } 
  
        // valid player? 
        if (player != currentTurn) { 
            return false; 
        } 
  
        if (sourcePiece.isWhite() != player.isWhiteSide()) { 
            return false; 
        } 
  
        // valid move? 
        if (!sourcePiece.canMove(board, move.getStart(), move.getEnd())) { 
            return false; 
        } 
  
        // taking? 
        Piece destPiece = move.getStart().getPiece(); 
        if (destPiece != null) { 
            destPiece.setTaken(true); 
            move.setPieceTaken(destPiece); 
        } 
  
        // castling? 
        if (sourcePiece != null && sourcePiece instanceof King && sourcePiece.isCastlingMove(move.getStart(), move.getEnd())) { 
            move.setCastlingMove(true); 
        } 
  
        // store the move 
        movesPlayed.add(move); 
  
        // move piece from the start box to the end box 
        move.getEnd().setPiece(move.getStart().getPiece()); 
        move.getStart().setPiece(null); 
        
        //win?
        if (destPiece != null && destPiece instanceof King) { 
            if (player.isWhiteSide()) { 
                this.setStatus(GameStatus.WHITE_WIN); 
            } 
            else { 
                this.setStatus(GameStatus.BLACK_WIN); 
            } 
        } 
  
        // set the current turn to the other player 
        if (this.currentTurn == players[0]) { 
        	move.getPieceMoved().increaseMoveCount();
            this.currentTurn = players[1]; 
        } 
        else { 
        	move.getPieceMoved().increaseMoveCount();
            this.currentTurn = players[0]; 
        } 
  
        return true; 
    }
    
    /**
     * @return board the game is played on
     * @ensures returns this.board
     */
    /*@
     @ ensures \result == this.board;
     @*/
    public final Board getBoard () {
    	return this.board;
    }
    
}
