package translator;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 *
 * @author Noor Khan (noorkhan_92@buaa.edu.cn)
 * @author Amjad (amjadphool@buaa.edu.cn)
 */
public class ModelGenerator {

    File inputFile;
    File outputFile;
    BufferedReader buffer;
    PrintWriter writer;
    List<String> listInput;
    List<String> listVar;
    List<String> listOutput;
    Map<Integer, String> inputVar = new HashMap<>();    //stores all input variable names
    Map<Integer, String> outputVar = new HashMap<>();    //stores all output variable names
    Map<Integer, String> initialisationVar = new HashMap<>();    //stores all initialized values of states variable names
    Map<Integer, String> statesVar = new HashMap<>();
    Map<Integer, String> evolutions = new HashMap<>();
    String nextStatement = "";
    String str;
    int altern = 0;
    int alterninitialisation = 0;
    int state = 1;
    int n = 0;

    public ModelGenerator() {
        try {
            inputFile = new File("andornotgate.smt2");
            buffer = new BufferedReader(new FileReader(inputFile));
            listInput = new ArrayList<>();
            listOutput = new ArrayList<>();
            listVar = new ArrayList<>();
            readInput();
            createOutput();
            compileInput();
        } catch (Exception ex) {
            System.err.println(ex.getMessage());
        }
    }

    private void readInput() {
        try {
            while ((str = buffer.readLine()) != null) {
                listInput.add(str);
            }
        } catch (IOException ex) {
            System.err.println(ex.getMessage());
        }
    }

    private void createOutput() {
        try {
            outputFile = new File(inputFile.getName().substring(0, inputFile.getName().length() - 4) + "z3z");
            outputFile.createNewFile();
        } catch (IOException ex) {
            System.err.println(ex.getMessage());
        }
    }

    private void compileInput() {
        //Reading input file for input variables, and generating its equavilant code in output file.
        listInput.forEach((s) -> {
            if (!";".equals(s.charAt(0))) {
                if (s.contains(";")) {
                    s = s.substring(0, s.indexOf(';'));
                }

                //to find input variables
                if (s.contains("_n")) {
                    if (!s.contains("extract")) {
                        inputVar.put(altern++, s.substring(s.indexOf("_n")).substring(2, s.substring(s.indexOf("_n")).indexOf('|')));
                    } else {
                        outputVar.put(altern, s.substring(s.indexOf("_n")).substring(2, s.substring(s.indexOf("_n")).indexOf('|')));
                        statesVar.put(altern++, "states_" + state++);
                    }
                } else if (s.contains("_i|")) {

                    for (int k : statesVar.keySet()) {
                        s = listInput.get(listInput.indexOf(s) + 1);
                        if (s.contains(Integer.toString(k))) {
                            if (s.contains("true")) {
                                initialisationVar.put(k, statesVar.get(k) + " = 1");
                            } else {
                                initialisationVar.put(k, statesVar.get(k) + " = -1");
                            }
                        }
                    }
                }

                if (s.contains("_t|")) {
                    int evoKey = 0;
                    for (int k : statesVar.keySet()) {
                        s = listInput.get(listInput.indexOf(s) + 1);
                        for (int key : statesVar.keySet()) {
                            if (s.contains("#" + Integer.toString(key))) {
                                evoKey = key;
                                evolutions.put(evoKey, statesVar.get(key) + " * ");
                            }
                        }

                        //evoluating next function...
                        nextStatement = findNextAltern(s.substring(s.indexOf("(|") + 2, s.indexOf("| state)")));

                        //check for input variables
                        int evoInput = 0;
                        String statement = nextStatement.substring(nextStatement.indexOf("ite"));
                        for (int input : inputVar.keySet()) {
                            int inputIndex = statement.indexOf("#" + input);
                            if(inputIndex>-1)
                            if (statement.substring(inputIndex, statement.substring(inputIndex).indexOf("| state") + inputIndex).equals("#" + input)) {
                                evoInput = input;
                                evolutions.put(evoKey, evolutions.get(evoKey) + "(when " + inputVar.get(input) + ") "
                                        + "+ (1 - (when " + inputVar.get(input) + ")) * " + statesVar.get(evoKey));
                                statement = statement.substring(statement.indexOf("ite"));
                            }
                        }

                        //this line gets substring after ite and its given input to be evaluated...
                        nextStatement = nextStatement.substring(nextStatement.indexOf("#" + Integer.toString(evoInput)) + 4, nextStatement.length());
                        // this line finds next statement after ite...
                        nextStatement = findNextAltern(nextStatement.substring(nextStatement.indexOf("|") + 1, nextStatement.indexOf("| state")));
                        String condition = nextStatement.substring(nextStatement.indexOf("Bool (") + 6, nextStatement.indexOf("Bool (") + 9);
                        //calling the find condition method to find output for given conditions like NOT AND etc
                        findCondition(condition, evoKey);
                    }
                }
            }
        });

        printToOutputList();

        listOutput.add("constraints: [ ];");
        listOutput.add("controllables: [ ];");
        listOutput.add("free_cond: [ ];");

        generateOutput();
    }

    private String findNextAltern(String altern) {
        for (String s : listInput) {
            if (s.contains(altern)) {
                return s;
            }
        }

        return null;
    }

    //finding conditional statment...
    private void findCondition(String condition, int evoKey) {
        List<String> requireState = new ArrayList<>();
        //finding the list of states given in the conditions like not or and.
        for (int k : statesVar.keySet()) {
            if (nextStatement.contains("#" + Integer.toString(k))) {
                requireState.add(statesVar.get(k));
            }
        }
        //finding the list of input variable given for the condition in and, or...
        for (int k : inputVar.keySet()) {
            if (nextStatement.contains("#" + Integer.toString(k))) {
                requireState.add(inputVar.get(k));
            }
        }
        
        switch (condition.toUpperCase()) {
            case "NOT": {
                evolutions.put(evoKey, "not " + "(" + requireState.get(0) + ")" + evolutions.get(evoKey).substring(8));
                break;
            }
            case "AND": {
                String andStatement = "";
                for (String s : requireState) {
                    andStatement = andStatement + s + " and ";
                }
                andStatement = andStatement.substring(0, andStatement.length() - 5);
                evolutions.put(evoKey, "(" + andStatement + ")" + evolutions.get(evoKey).substring(8));
                break;
            }

            case "OR ": {
                String orStatement = "";
                for (String s : requireState) {
                    orStatement = orStatement + s + " or ";
                }
                orStatement = orStatement.substring(0, orStatement.length() - 4);
                evolutions.put(evoKey, "(" + orStatement + ")" + evolutions.get(evoKey).substring(8));
                break;
            }

            default: {
                break;
            }
        }
    }

    //to generate output file
    private void generateOutput() {
        try {
            writer = new PrintWriter(outputFile);
        } catch (FileNotFoundException ex) {
            System.out.println(ex.getMessage());
        }
        listOutput.forEach((s) -> {
            writer.println();
            if (s.contains(",") && s.contains("evolutions")) {
                List<String> lineList = Arrays.asList(s.split(","));
                lineList.forEach((String line) -> {
                    if (line.equals(lineList.get(lineList.size() - 1))) {
                        writer.println(line);
                    } else {
                        writer.println(line + ",");
                    }
                });
            } else {
                writer.println(s);
            }
        });
        writer.close();
        System.out.println("The program run succesfully and the output file with extension z3z generated...");
    }

    /*
    print statements to output list ready for the target language,
    then will be added to the output file...
     */
    private void printToOutputList() {

        int indexOfDeclare;
        int indexOfEvents;
        int indexOfStates;
        int indexOfinitialisations;
        int indexOfEvolutions;

        listOutput.add("declare(");
        listOutput.add("events: [");
        listOutput.add("states: [");
        listOutput.add("initialisations: [");
        listOutput.add("evolutions: [");
        indexOfDeclare = listOutput.indexOf("declare(");
        indexOfEvents = listOutput.indexOf("events: [");
        indexOfStates = listOutput.indexOf("states: [");
        indexOfinitialisations = listOutput.indexOf("initialisations: [");
        indexOfEvolutions = listOutput.indexOf("evolutions: [");
        inputVar.values().forEach((s) -> {
            listOutput.set(indexOfDeclare, listOutput.get(indexOfDeclare) + s + ", ");
            listOutput.set(indexOfEvents, listOutput.get(indexOfEvents) + s + ", ");
        });

        //adding states or memory location for output variables...
        for (String s : statesVar.values()) {
            listOutput.set(indexOfStates, listOutput.get(indexOfStates) + s + ", ");
            listOutput.set(indexOfDeclare, listOutput.get(indexOfDeclare) + s + ", ");
        }

        //adding initialisation values to states...
        for (String s : initialisationVar.values()) {
            listOutput.set(indexOfinitialisations, listOutput.get(indexOfinitialisations) + s + ", ");
        }

        for (String s : evolutions.values()) {
            listOutput.set(indexOfEvolutions, listOutput.get(indexOfEvolutions) + s + ", ");
        }

        String declare = listOutput.get(indexOfDeclare);
        listOutput.set(indexOfDeclare, declare.substring(0, declare.lastIndexOf(',')) + ");");
        String events = listOutput.get(indexOfEvents);
        listOutput.set(indexOfEvents, events.substring(0, events.lastIndexOf(",")) + "];");
        String states = listOutput.get(indexOfStates);
        listOutput.set(indexOfStates, states.substring(0, states.lastIndexOf(",")) + "];");
        String initialisations = listOutput.get(indexOfinitialisations);
        listOutput.set(indexOfinitialisations, initialisations.substring(0, initialisations.lastIndexOf(",")) + "];");

        //finalizing evolotions statement and adding to the output list...
        String evolution = listOutput.get(indexOfEvolutions);
        listOutput.set(indexOfEvolutions, evolution.substring(0, evolution.lastIndexOf(", ")) + "];");
        //printSomething(indexOfEvents, null);
    }

    //Testing method....
    private void printSomething(int a, String s) {
        System.out.println(listOutput.get(a));
    }

    public static void main(String args[]) {
        ModelGenerator generator = new ModelGenerator();
    }

}
