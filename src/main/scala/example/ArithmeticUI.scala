// inserts binary arithmetic operations between user input numbers, to make equations
// readme and problem statement is at https://github.com/danlaudk/my-scalajs-public/
// or simply use it at https://danlaudk.github.io/my-scalajs-public/

// 3 parts : an object for the Arithmetic algorithm, an object for the UI, and classes/objects for Signals to make UI reactive
// the first part, 150 lines, is most relevant to recurse center (i think) 
object Arithmetic {
  // a symbol is either a number or a binary operator
  trait Symbol {
    override def toString: String
  }
  case class Number(n: Double) extends Symbol {
    override def toString() = this match {
      case Number(t) => t.toString
      case _ => this.toString
    }
  }
  case class Operator(f: Function2[Double, Double, Double]) extends Symbol {
    override def toString() = this match { 
      case Operator(t) if t(3, 2) == 5.0 => "+"
      case Operator(t) if t(3, 2) == 6.0 => "*"
      case Operator(t) if t(3, 2) == 1.0 => "-"
      case Operator(t) if t(3, 2) == 1.5 => "/"
      case _ => this.toString()
    }
  }
  /////////// constants // the allowable arithmetic  ///////////
  val f: List[(Double, Double) => Double] = List(_ + _, _ * _, _ / _, _ - _)

  /////////// string functions for display ///////////
  def joinAndBracket(num1: String, op: Operator, num2: String): String =
  "(" + num1.toString + op.toString + num2.toString + ")"

  def stripBracket(s: String): String =
    if (s.isEmpty || s.head != '(') s
    else s.tail.init // precautionary

  // Given 2 lists of symbols (lhs, rhs), returns a string, which is given eventually by the only element after reducing a stack of strings
  def stringify(solution: Tuple2[List[Symbol], List[Symbol]]): String = {
    val (lhsSymbols, rhsSymbols) = (solution._1, solution._2)
    def pullSymbolsFromQ(q: List[Symbol], stack: List[String]): String = q match {
      case Nil => stripBracket(stack.head)
      case Number(first) :: tail => pullSymbolsFromQ(tail, first.toString :: stack) // keep nums & do to string in joinandbracket
      case Operator(operation) :: tail => {
        pullSymbolsFromQ(tail, joinAndBracket(stack(1), Operator(operation), stack.head) :: stack.drop(2))
      }
      case _ => throw new Exception("first in q is not a symbol and stack length is " + stack.length)
    }
    pullSymbolsFromQ(lhsSymbols, Nil) +
      " = " +
      pullSymbolsFromQ(rhsSymbols, Nil)
  }

  def printSolutions(solutions: Seq[Tuple2[List[Symbol], List[Symbol]]], s: String): String =
    if (solutions.isEmpty) s
    else printSolutions(solutions.tail, s + "\n" + stringify(solutions.head))

  /////////// function for calculating, more recursion ///////////
  def evalExpression(seqSymbols: List[Symbol]): Double = {
    def pullSymbolsFromQ(q: List[Symbol], stack: List[Double]): Double = q match {
      case Nil => stack.head
      case Number(first) :: tail => pullSymbolsFromQ(tail, first :: stack)
      case Operator(operation) :: tail => {
        if (stack.length < 2) throw new Exception("seq " + seqSymbols.map(_.toString) + "operation " + operation.toString() + " stack(1)head " + stack.head.toString)
        pullSymbolsFromQ(tail, operation(stack(1), stack.head) :: stack.drop(2))
      }
      case _ => throw new Exception("first in q is not a symbol and stack length is " + stack.length)
    }
    pullSymbolsFromQ(seqSymbols, Nil)
  }

  /////////// functions for building up expressions or 'arrays' of 'symbols' ///////////
  def getProduct[T](input: List[List[T]]): List[List[T]] = input match {
    //getProduct on a table of allowable elements, to get cartesian product. from stackoverflow
    case Nil => Nil
    case head :: Nil => head.map(_ :: Nil)
    case head :: tail => for (elem <- head; sub <- getProduct(tail)) yield elem :: sub
  }

  //  returns cartesian product of "possible" numbers of operators in each gap after a number.
  // 'count' is everywhere the count of numbers, in the expression being built
  def buildSlotsInGapsForOperators(count: Int): List[List[Int]] = {
    if (count < 2) return List(List()) // dummy singleton to avoid an empty generator being skipped over in for-comprehension
    val repeatedInts = (0 until count).map(i => (0 to i).toList).toList // num gaps is count

    // cartesian product, then filter where (cumsum <= index) bc can't have more symbols than numbers (to the left of any point)
    // then filter to have valid number of operators
    getProduct(repeatedInts).
      filter(li => li.scanLeft(0)(_ + _).tail.zipWithIndex.forall(t => t._1 <= t._2)).
      filter(gapList => gapList.sum == count - 1 )
  }

  // returns sequences of operators
  def buildOperators(count: Int, f: List[Operator]): List[List[Operator]] = {
    if (count == 1) return List(List()) //dummy List so that it's not skipped over in for-comprehension
    val repeatedOperators = List.tabulate(count - 1)(_ => f)
    getProduct(repeatedOperators)
  }

  // using above, build sequences of symbols
  def buildSymbols(numbers: List[Double], f: List[(Double, Double) => Double]) = {
    val count = numbers.length
    val numList = numbers.map(i => Number(i))
    val signList = f.map(i => Operator(i))
    for {
      operatorList <- buildOperators(count, signList)
      gapList <- buildSlotsInGapsForOperators(count) // each of length count
      if gapList.sum == count - 1 | count == 1
    } yield assembleArray(operatorList, gapList, numList)
  }
  // guts of buildSymbols
  // After each number is a gap, and for the number of operators assigned to the gap (gapList), fill with operators from operatorList
  // the array of numbers and operators.
  def assembleArray(operatorList: List[Symbol], gapList: List[Int], numberList: List[Symbol]): List[Symbol] = {
    val count = numberList.length
    if (count == 1) return List(numberList.head)
    if (count - 1 != operatorList.length | count != gapList.length | gapList.sum != count - 1) throw new Exception("gapList.sum is " + gapList.sum.toString + " gaplist.elgnth is " + gapList.length.toString)
    val arr: Array[Symbol] = Array.ofDim[Symbol](count + count - 1)
    arr(0) = numberList.head
    var operatorsUsed = 0
    for (numbersUsed <- 1 until count) {
      arr(numbersUsed + operatorsUsed) = numberList(numbersUsed)
      for (j <- 0 until gapList(numbersUsed)) {
        arr(numbersUsed + 1 + operatorsUsed) = operatorList(operatorsUsed)
        operatorsUsed += 1
      }
    }
    arr.toList
  }

  /////////// put it all together ///////////
  def findEqualities(provided: List[Double]): String = {
    val allValidEquations = for {
      countOfLHS <- 1 until provided.length // until, because need to save a term for the RHS
      lhsNumbers = provided.take(countOfLHS)
      rhsNumbers = provided.drop(countOfLHS)

      validEqnGivenCount <- for {
        seqSymbolsLHS <- buildSymbols(lhsNumbers, f)
        seqSymbolsRHS <- buildSymbols(rhsNumbers, f)
        lhs = evalExpression(seqSymbolsLHS)
        rhs = evalExpression(seqSymbolsRHS)
        if lhs == rhs
      } yield (seqSymbolsLHS, seqSymbolsRHS)
    } yield validEqnGivenCount

    val numSolns = allValidEquations.length

    if (allValidEquations.isEmpty) return "no solutions"
    else return (
      "there are " + numSolns.toString + " solutions and they are " +
        printSolutions(allValidEquations, "")
      )
  }
}

// part 2 : code for UI
// code from here on is only to get it published onto a working webpage
import scala.scalajs.js
import org.scalajs.dom
import org.scalajs.dom.html
import dom.document

object ArithmeticUI extends js.JSApp {
  /**
    * Created by dlau on 1/3/17. html is modelled from Coursera tweetlength Signals module
    */
    def main(): Unit = {
      try {
        val textSignal = Signal(textAreaValueSignal("tweettext")().split(Array(';', ',', ':', ' ')).
          map(_.trim).
          map(toDbl).
          toList.
          flatten)

        val remainingCharsArea =
          document.getElementById("tweetremainingchars").asInstanceOf[html.Span]

        val remainingCount = Signal(Arithmetic.findEqualities(textSignal()))
        Signal {
          remainingCharsArea.textContent = remainingCount().toString
        }
      } catch {
        case th: Throwable =>
          th.printStackTrace()
      }
    }

    def toDbl(s: String):Option[Double] = {
      try {
        Some(s.toDouble)
      } catch {
        case e: NumberFormatException => None
      }
    }
 ////////////////////////// end my helpers //////////////////////////////

// part 3 : the UI reactive framework
//////////////////////////  From here on it's purely Coursera code //////////////////////////////
    def elementById[A <: js.Any](id: String): A =
    document.getElementById(id).asInstanceOf[A]

    def elementValueSignal(element: html.Element,
                           getValue: () => String): Signal[String] = {
      var prevVal = getValue()
      val value = new Var(prevVal)
      val onChange = { (event: dom.Event) =>
        // Reconstruct manually the optimization at the root of the graph
        val newVal = getValue()
        if (newVal != prevVal) {
          prevVal = newVal
          value() = newVal
        }
      }
      element.addEventListener("change", onChange)
      element.addEventListener("keypress", onChange)
      element.addEventListener("keyup", onChange)
      value
    }

    def inputValueSignal(input: html.Input): Signal[String] =
      elementValueSignal(input, () => input.value)

    def textAreaValueSignal(textAreaID: String): Signal[String] = {
      val textArea = elementById[html.TextArea](textAreaID)
      elementValueSignal(textArea, () => textArea.value)
    }
}

import scala.util.DynamicVariable

class Signal[T](expr: => T) {
  import Signal._

  private var myExpr: () => T = _
  private var myValue: T = _
  private var observers: Set[Signal[_]] = Set()
  private var observed: List[Signal[_]] = Nil
  update(expr)

  protected def computeValue(): Unit = {
    for (sig <- observed)
      sig.observers -= this
    observed = Nil
    val newValue = caller.withValue(this)(myExpr())
    /* Disable the following "optimization" for the assignment, because we
   * want to be able to track the actual dependency graph in the tests.
   */
    //if (myValue != newValue) {
    myValue = newValue
    val obs = observers
    observers = Set()
    obs.foreach(_.computeValue())
    //}
  }

  protected def update(expr: => T): Unit = {
    myExpr = () => expr
    computeValue()
  }

  def apply() = {
    observers += caller.value
    assert(!caller.value.observers.contains(this), "cyclic signal definition")
    caller.value.observed ::= this
    myValue
  }
}

class Var[T](expr: => T) extends Signal[T](expr) {
  override def update(expr: => T): Unit = super.update(expr)
}

object Var {
  def apply[T](expr: => T) = new Var(expr)
}

object NoSignal extends Signal[Nothing](???) {
  override def computeValue() = ()
}

object Signal {
  val caller = new DynamicVariable[Signal[_]](NoSignal)

  def apply[T](expr: => T) = new Signal(expr)
}



