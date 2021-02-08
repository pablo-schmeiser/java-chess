package players;

/**
 * Class representing computer players.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
public class ComputerPlayer extends Player {
	
	/**
	 * Constructor using the Player super-constructor.
	 * @param whiteSide Boolean representing if the player is playing white or black
	 */
	/*@
	 @ requires whiteSide != null;
	 @*/
	public ComputerPlayer (final boolean whiteSide) { 
        super(whiteSide, false);
    }

}
