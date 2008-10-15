/*
 * Author:     Ingo Schroeder
 * EMail:      ingo.schroeder@informatik.uni-hamburg.de
 * Date:       29.2.96
 * Program:    MineSweeper applet
 * Status:     beta
 * Copyright:  GNU General Public license, Version 2
 *
 * Please mail me bug reports and suggestions. Thank You.
 *
 */

import java.awt.*;
import java.awt.image.*;
import java.net.*;
import java.applet.*;

public class MineSweeper extends Applet {

  // -----------------------------------------------------------------------
  // -- state variable
  static final byte INVALID = 0;
  static final byte RUNNING = 1;
  static final byte GAMEOVER = 2;
  // -- bomb? (should this be boolean?)
  static final byte NOBOMB = 0;
  static final byte BOMB = 1;
  // -- user marking
  static final byte UNMARKED = 0;
  static final byte MARKED = 1;
  static final byte CLEARED = 2;
  // defaults
  static final byte ROWS = 16;
  static final byte COLS = 30;
  static final byte SIZE = 16;

  // -----------------------------------------------------------------------
  private byte state;
  // board representation
  private byte hasBomb[][];
  private byte userMarking[][];
  private byte neighborBombs[][];

  private Image noImage[];
  private Image buttonImage, flagImage, bombImage, boomImage, nobombImage;

  // board size
  private int rows;
  private int cols;
  private int noOfBombs;
  // remember last modifier field
  private int lastModifiers = 0;
  // remember last row/column
  private int or = -1;
  private int oc = -1;
  

  // -----------------------------------------------------------------------
  public void init() {

    rows = this.size().height / SIZE;
    cols = this.size().width / SIZE;

    // no of bombs depends on board size
    noOfBombs = (int)rows*cols/5;

    hasBomb = new byte[rows][cols];
    userMarking = new byte[rows][cols];
    neighborBombs = new byte[rows][cols];

    noImage = new Image[9];

    // no valid state so far
    state = INVALID;

    // get images
    for (int i = 0; i < 9; i++) {
      noImage[i] = getImage(getCodeBase(),"./images/no-" + i + ".gif");
    }
    buttonImage = getImage(getCodeBase(),"./images/button.gif");
    flagImage = getImage(getCodeBase(), "./images/flag.gif");
    bombImage = getImage(getCodeBase(), "./images/bomb.gif");
    boomImage = getImage(getCodeBase(), "./images/boom.gif");
    nobombImage = getImage(getCodeBase(),"./images/nobomb.gif");

    // start game
    newGame();
  }

  // -----------------------------------------------------------------------
  public void update(Graphics g) {
    // avoid flicker
    paint(g);
  }

  // -----------------------------------------------------------------------
  public void paint(Graphics g) {
    for (int i = 0; i < rows; i++) {
      for (int j = 0; j < cols; j++) {
        if (userMarking[i][j] == UNMARKED) {
          if ( (state == GAMEOVER) && (hasBomb[i][j] == BOMB) ) {
            g.drawImage(bombImage, j*SIZE, i*SIZE, this);
          } else {
            g.drawImage(buttonImage, j*SIZE, i*SIZE, this);
          }
        }
        if (userMarking[i][j] == CLEARED) {
          if ( (state == GAMEOVER) && (hasBomb[i][j] == BOMB) ) {
            g.drawImage(boomImage, j*SIZE, i*SIZE, this);
          } else {
            g.drawImage(noImage[neighborBombs[i][j]], j*SIZE, i*SIZE, this);
          }
        }
        if (userMarking[i][j] == MARKED) {
          if ( (state == GAMEOVER) && (hasBomb[i][j] == NOBOMB) ) {
            g.drawImage(nobombImage, j*SIZE, i*SIZE, this);
          } else {
            g.drawImage(flagImage, j*SIZE, i*SIZE, this);
          }
        }
      }
    }
  }

  // -----------------------------------------------------------------------
  public boolean handleEvent(Event evt) {
    int r = (int)Math.floor((double)evt.y/SIZE);
    int c = (int)Math.floor((double)evt.x/SIZE);

    //System.out.print("Event x/y=(" + evt.x + "," + evt.y + ")");
    //System.out.println(" r/c=(" + r + "," + c +") mod=" + evt.modifiers);

    // out of area
    if ( !((r < rows) && (r >= 0) && (c < cols) && (c >= 0)) ) 
      return true;
 
    // The game is over and the user clicks in the applet.
    if (state == GAMEOVER) {
      if (evt.id == Event.MOUSE_UP) {
        newGame();
        repaint();
      }
      return true;
    }

    // state == RUNNING
    if (evt.id == Event.MOUSE_UP) {
      // shift key or right mouse button (is this portable?)
      if (evt.shiftDown() || ((lastModifiers & 4) == 4) ) {
        if (userMarking[r][c] == UNMARKED) {
          // place flag
          userMarking[r][c] = MARKED;
          getGraphics().drawImage(flagImage, c*SIZE, r*SIZE, this);
        } else if (userMarking[r][c] == MARKED) {
          // clear flag
          userMarking[r][c] = UNMARKED;
          getGraphics().drawImage(buttonImage, c*SIZE, r*SIZE, this);
        }
      } else if (userMarking[r][c] == UNMARKED) {
        // clear field
        userMarking[r][c] = CLEARED;
        if (hasBomb[r][c] == NOBOMB) {
          clearArea(r, c); 
        } else {
          state = GAMEOVER;
          getGraphics().drawImage(boomImage, c*SIZE, r*SIZE, this);
          repaint();
        }
      }
    } else if (evt.id == Event.MOUSE_DOWN) {
      // I have to remember the modifiers here because Netscape does not set it
      // correctly for a MOUSE_UP event.
      lastModifiers = evt.modifiers;
    }
    // return super.handleEvent(evt);
    return true;

/*
    if ( (evt.id == Event.MOUSE_DOWN) && !evt.shiftDown() ) {
        if ( (r < rows) && (r >= 0) && (c < cols) && (c >= 0) ) {
          if ( board[r*cols + c].isUnmarked() ) {
              getGraphics().drawImage(noImage[0], c*SIZE, r*SIZE, this);
          }
          or = r;
          oc = c;
        }
    } else 
    if ((evt.id == Event.MOUSE_DRAG) && !evt.shiftDown() ) {
        // System.out.println("mouseDrag " + evt );
        if ( (or != r) || (oc != c) ) {
          // restore 
          // System.out.println("restore "+r+"/"+c+"/"+or+"/"+oc);
          if ( (or < rows) && (or >= 0) && (oc < cols) && (oc >= 0) &&
               board[or*cols + oc].isUnmarked() ) {
              getGraphics().drawImage(buttonImage, oc*SIZE, or*SIZE, this);
          }
          if  ( (r < rows) && (r >= 0) && (c < cols) && (c >= 0) &&
                board[r*cols + c].isUnmarked() ) {
              getGraphics().drawImage(noImage[0], c*SIZE, r*SIZE, this);
          }
        }
        or = r;
        oc = c;
    } else
    if (evt.id == Event.MOUSE_UP) {
        // mouse clicks
        if ( (r < rows) && (r >= 0) && (c < cols) && (c >= 0) ) {
          if (board[r*cols + c].isUnmarked()) {
              getGraphics().drawImage(buttonImage, c*SIZE, r*SIZE, this);
          }
        }
    }
*/
  }

  // -----------------------------------------------------------------------
  public void clearArea(int r, int c) {
    userMarking[r][c] = CLEARED;
    getGraphics().drawImage(noImage[neighborBombs[r][c]],c*SIZE,r*SIZE,this);
    if (neighborBombs[r][c] == 0) {
      for (int i = -1; i <= 1; i++) {
        for (int j = -1; j <= 1; j++) {
          if ( (r+i<rows) && (r+i>=0) && (c+j<cols) && (c+j>=0) && 
               (userMarking[r+i][c+j] != CLEARED) ) {
            clearArea(r + i, c + j);
          }
        }
      }
    }
  }

  // -----------------------------------------------------------------------
  public void newGame() {
    for (int i = 0; i < rows; i++) {
      for (int j = 0; j < cols; j++) {
        hasBomb[i][j] = NOBOMB;
        userMarking[i][j] = UNMARKED;
        neighborBombs[i][j] = (byte)0;
      }
    }
    // place bombs
    for (int n = 0; n < noOfBombs; n++) {
      int b = (int)(Math.random() * (cols*rows - n - 1));
      //int b = cols*rows - n - 1;
      int r = 0;
      int c = 0;
      while ( (b != 0) || (hasBomb[r][c] == BOMB) ) {
        //System.out.println("r/c/b = "+r+"/"+c+"/"+b); 
        if (hasBomb[r][c] == NOBOMB)
          b--; 
        if (++c >= cols) {
          c = 0;
          r++;
        }
      }
      hasBomb[r][c] = BOMB;
      // update bomb counters
      for (int i = -1; i <= 1; i++) {
        for (int j = -1; j <= 1; j++) {
          if ((r+i>=0)&&(r+i<rows)&&(c+j>=0)&&(c+j<cols)&& !(i==0 && j==0))
            neighborBombs[r+i][c+j]++;
        }
      }
    }
    state = RUNNING;
    //state = GAMEOVER;
  }

  // -----------------------------------------------------------------------
  public Dimension minimumSize() {
    return new Dimension(cols*SIZE, rows*SIZE);
  }
  public Dimension preferredSize() {
    return minimumSize();
  }
  // -----------------------------------------------------------------------
  public String getAppletInfo() {
    return "Minesweeper by Ingo Schroeder";
  }
}

// -------------------------------------------------------------------------
// -------------------------------------------------------------------------







