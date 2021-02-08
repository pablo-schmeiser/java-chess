package game;

/**
 * Class representing a position with X- and Y-Coordinates on a chessboard.
 * @author Pablo Schmeiser
 * @version 1.0.0
 */
/*@
 @ invariant this.posX != null && this.posX > 7 && this.posX < 0;
 @ invariant this.posY != null && this.posY > 7 && this.posY < 0;
 @*/
public /*@ pure */ class Position {
	private final /*@ non_null */ Integer posX;
	private final /*@ non_null */ Integer posY;
	
	/**
	 * @throws NullPointerException Coordinates may not be null.
	 * @throws IllegalArgumentException Coordinates may not be negative or greater than 7.
	 * @param posX X-Coordinate to set the posX attribute to
	 * @param posY Y-Coordinate to set the posY attribute to
	 * @ensures this.posX == posX && this.posY == posY
	 */
	/*@
	 @ ensures this.posX == posX && this.posY == posY;
	 @ signals (NullPointerException e) posX == null || posY == null;
	 @ signals (IndexOutOfBoundsException e2) posX < 0 || posX > 7 || posY < 0 || posY > 7;
	 @ assignable this.posX, this.posY;
	 @*/
	public /*@ pure */ Position (final Integer posX, final Integer posY) {
		if (posX == null || posY == null) {
			throw new NullPointerException("Coordinates may not be null.");
		};
		if (posX < 0 || posX > 7 || posY < 0 || posY > 7) {
			throw new IndexOutOfBoundsException("Coordinates may not be negative or greater than 7.");
		};
		
		this.posX = posX;
		this.posY = posY;
	}
	
	/**
	 * @return X coordinate of the position
	 * @ensures returns this.posX
	 */
	/*@
	 @ ensures \result == this.posX;
	 @*/
	public final /*@ pure */ Integer getPosX () {
		return this.posX;
	}
	
	/**
	 * @return Y coordinate of the position
	 * @ensures returns this.posX
	 */
	/*@
	 @ ensures \result == this.posY;
	 @*/
	public final /*@ pure */ Integer getPosY () {
		return this.posY;
	}
	
}
