package players;

/**
 * Class representing human players.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
public class HumanPlayer extends Player {

	/**
	 * Constructor using the Player super-constructor.
	 * @param whiteSide Boolean representing if the player is playing white or black
	 */
	/*@
	 @ requires whiteSide != null;
	 @*/
	public HumanPlayer (final boolean whiteSide) {
        super(whiteSide, true);
    }
	
}
