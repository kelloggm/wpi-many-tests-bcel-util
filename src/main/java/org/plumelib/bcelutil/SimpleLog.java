package org.plumelib.bcelutil;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

/**
 * A logging class with the following features.
 *
 * <ul>
 *   <li>Can be enabled and disabled (when disabled, all operations are no-ops),
 *   <li>Can indent/exdent log output,
 *   <li>Writes to a file or to standard output, and
 *   <li>Can provide a stack trace.
 * </ul>
 */
public final class SimpleLog {

  /** If false, do no output. */
  public boolean enabled;

  /** The current indentation level. */
  private int indentLevel = 0;
  /** Indentation string for one level of indentation. */
  private static final String INDENT_STR_ONE_LEVEL = "  ";

  /**
   * Cache for the current indentation string, or null if needs to be recomputed. Never access this
   * directly; always call {@link #getIndentString}.
   */
  private String indentString = null;
  /** Cache of indentation strings that have been computed so far. */
  private List<String> indentStrings;

  /** Create a new SimpleLog object with logging to standard out enabled. */
  public SimpleLog() {
    this(true);
  }

  /**
   * Create a new SimpleLog object with logging to standard out.
   *
   * @param enabled true if the logger starts out enabled
   */
  public SimpleLog(boolean enabled) {
    this.enabled = enabled;
    indentStrings = new ArrayList<String>();
    indentStrings.add("");
  }

  /**
   * Returns true if logging is enabled.
   *
   * @return true if logging is enabled
   */
  public boolean enabled() {
    return enabled;
  }

  /**
   * Log a message. The message is prepended with the current indentation string. The
   * indentation is only applied at the start of the message, not for every line break within the
   * message.
   *
   * @param format format string for message
   * @param args values to be substituted into format
   */
  public void log(String format, Object... args) {
    if (enabled) {
      System.out.print(getIndentString());
      System.out.printf(format, args);
    }
  }

  /** Print a stack trace to the log. */
  public void logStackTrace() {
    if (enabled) {
      Throwable t = new Throwable();
      t.fillInStackTrace();
      StackTraceElement[] stackTrace = t.getStackTrace();
      for (int ii = 2; ii < stackTrace.length; ii++) {
        StackTraceElement ste = stackTrace[ii];
        System.out.printf("%s  %s%n", getIndentString(), ste);
      }
    }
  }

  /**
   * Returns the current indentation string.
   *
   * @return the current indentation string
   */
  private String getIndentString() {
    assert enabled;
    if (indentString == null) {
      for (int i = indentStrings.size(); i <= indentLevel; i++) {
        indentStrings.add(indentStrings.get(i - 1) + INDENT_STR_ONE_LEVEL);
      }
      indentString = indentStrings.get(indentLevel);
    }
    return indentString;
  }

  /** Increases indentation by one level. */
  public void indent() {
    if (enabled) {
      indentLevel++;
      indentString = null;
    }
  }

  /** Decreases indentation by one level. */
  public void exdent() {
    if (enabled) {
      if (indentLevel == 0) {
        log("Called exdent when indentation level was 0.");
        logStackTrace();
      } else {
        indentLevel--;
        indentString = null;
      }
    }
  }

  /** Resets indentation to none. Has no effect if logging is disabled. */
  public void resetIndent() {
    if (enabled) {
      indentLevel = 0;
      indentString = "";
    }
  }
}
