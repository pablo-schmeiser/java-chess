package players;

/**
 * Class representing Players.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
 @ invariant this.whiteSide != null;
 @ invariant this.humanPlayer != null;
 @*/
public abstract class Player {
	private boolean whiteSide;
	private final boolean humanPlayer;
	
	/**
	 * @param whiteSide Boolean representing if the player is playing white or black
	 * @param humanPlayer Boolean representing if the player is a human or a computer
	 */
	/*@
	 @ requires whiteSide != null;
	 @ requires whiteSide != null;
	 @ ensures this.whiteSide == whiteSide;
	 @ ensures this.humanPlayer == humanPlayer;
	 @*/
	public Player (final boolean whiteSide, final boolean humanPlayer) {
		this.setWhiteSide(whiteSide);
		this.humanPlayer = humanPlayer;
	}
	
	/**
	 * Gets if the person is playing white or black.
	 * @return this.whiteSide
	 */
	/*@
	 @ ensures \result == this.whiteSide;
	 @*/
	public boolean isWhiteSide () { 
        return this.whiteSide; 
    } 
	
	/**
	 * Gets if the person is a human or a computer.
	 * @return this.whiteSide
	 */
	/*@
	 @ ensures \result == this.humanPlayer;
	 @*/
    public boolean isHumanPlayer () { 
        return this.humanPlayer; 
    }
    
    /**
     * @param whiteSide Boolean to the whiteSide attribute to
     * @ensures this.whiteSide == whiteSide
     */
    /*@
     @ requires whiteSide != null;
     @ ensures this.whiteSide == whiteSide;
     @*/
    public final void setWhiteSide (final boolean whiteSide) {
    	this.whiteSide = whiteSide;
    }
    
}
