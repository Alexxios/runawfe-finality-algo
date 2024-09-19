package ru.runa.gpd.algorithms.finality;

import ru.runa.gpd.PluginLogger;
import ru.runa.gpd.algorithms.ListUnprocessedStates;
import ru.runa.gpd.algorithms.TransitionVector;
import ru.runa.gpd.algorithms.Vector;
import ru.runa.gpd.lang.model.*;
import ru.runa.gpd.lang.model.Timer;
import ru.runa.gpd.lang.model.bpmn.ParallelGateway;
import ru.runa.gpd.lang.model.jpdl.Fork;
import ru.runa.gpd.lang.model.jpdl.Join;

import java.util.*;

public class CheckCorrectFinalityAlgorithm {
    private static final boolean DEBUG = "true".equals(System.getProperty("ru.runa.gpd.algorithms.checkCorrectFinality.debug"));
    List<Transition> transitions;
    List<Node> nodes;
    List<Vector> vVectorList = new ArrayList<Vector>();
    List<Vector> graphList = new ArrayList<Vector>();
    ListUnprocessedStates listUnprocessedStates = new ListUnprocessedStates();
    List<TransitionVector> transitionVectors = new ArrayList<TransitionVector>();

    Map<Vector, List<Vector>> vectorGraph = new HashMap<>();
    Map<Vector, Boolean> visited = new HashMap<>();

    List<Transition> dangerousTransitions;

    public CheckCorrectFinalityAlgorithm(List<Transition> transitions, List<Node> nodes) {
        this.transitions = transitions;
        this.nodes = nodes;

        populateVectorList();
        Vector vector = new Vector(transitions.size() + 1);
        vector.setElementValue(0, 1);
        graphList.add(vector);
    }

    public void startAlgorithm() {
        if (DEBUG) {
            StringBuilder str = new StringBuilder();
            str.append("CheckCorrectFinalityAlgorithm started.");
            str.append("\n");
            str.append("The list of V vectors contains:");
            str.append("\n");
            for (Vector vVector : vVectorList) {
                str.append(vVector.toString());
                str.append("\n");
            }
            PluginLogger.logInfo(str.toString());
        }
        List<Vector> startVectorList = new ArrayList<Vector>();
        Vector vector = new Vector(transitions.size() + 1);
        vector.setElementValue(0, 1);
        startVectorList.add(vector);
        Vector initGraphVector = new Vector(transitions.size() + 1);
        initGraphVector.setElementValue(0, 1);
        graphList.add(initGraphVector);
        listUnprocessedStates.addInList(startVectorList);

        while (listUnprocessedStates.isFirstObjExist()) {
            Vector uVector = listUnprocessedStates.getFirstObj();

            if (DEBUG) {
                StringBuilder str = new StringBuilder();
                str.append("Current U vector is:");
                str.append("\n");
                str.append(uVector.toString());
                str.append("\n");
                PluginLogger.logInfo(str.toString());
            }
            List<Vector> listIntermediateVectors = new ArrayList<Vector>();
            for (Vector vVector : vVectorList) {
                Vector tempVector = uVector.getVectorsSum(vVector);
                if (!tempVector.isNegativeNumberExist() && !tempVector.isNullValueVector()) {
                    listIntermediateVectors.add(tempVector);
                }
            }
            if (DEBUG) {
                StringBuilder str = new StringBuilder();
                str.append("Intermediate vectors are:");
                str.append("\n");
                for (Vector intermediateVector : listIntermediateVectors) {
                    str.append(intermediateVector.toString());
                    str.append("\n");
                }
                PluginLogger.logInfo(str.toString());
            }
            StringBuilder str = new StringBuilder();
            List<Vector> equalVectors = new ArrayList<Vector>();
            for (Vector intermediateVector : listIntermediateVectors) {
                for (Vector graphVector : graphList) {
                    if (Arrays.equals(intermediateVector.getElements(), graphVector.getElements())) {
                        equalVectors.add(intermediateVector);
                        transitionVectors.add(new TransitionVector(uVector, graphVector));

                        List<Vector> tmpList = vectorGraph.getOrDefault(uVector, new ArrayList<>());
                        tmpList.add(graphVector);
                        vectorGraph.put(uVector, tmpList);

                        str.append("Create transition between: " + uVector.toString() + " and " + graphVector.toString());
                        str.append("\n");
                    }
                }
            }

            listIntermediateVectors.removeAll(equalVectors);

            for (Vector intermediateVector : listIntermediateVectors) {
                transitionVectors.add(new TransitionVector(uVector, intermediateVector));

                List<Vector> tmpList = vectorGraph.getOrDefault(uVector, new ArrayList<>());
                tmpList.add(intermediateVector);
                vectorGraph.put(uVector, tmpList);

                str.append("Create transition between: " + uVector.toString() + " and " + intermediateVector.toString());
                str.append("\n");
            }
            if (DEBUG) {
                PluginLogger.logInfo(str.toString());
            }
            graphList.addAll(listIntermediateVectors);
            listUnprocessedStates.addInList(listIntermediateVectors);
            listIntermediateVectors.clear();

            listUnprocessedStates.removeFirst();
            if (DEBUG) {
                str = new StringBuilder();
                str.append("List unprocessed vectors:");
                str.append("\n");
                for (Vector unprocessedVector : listUnprocessedStates.getList()) {
                    str.append(unprocessedVector.toString());
                    str.append("\n");
                }
                PluginLogger.logInfo(str.toString());
            }
        }

        if (DEBUG) {
            StringBuilder str = new StringBuilder();
            str.append("Graph of processed vectors:");
            str.append("\n");

            for (Vector uVector : vectorGraph.keySet()) {
                str.append(uVector.toString());
                str.append(": ");

                for (Vector vec : vectorGraph.get(uVector)) {
                    str.append(vec.toString());
                    str.append(" ");
                }
                str.append("\n");
            }
            str.append("\n");
            PluginLogger.logInfo(str.toString());
        }

        dangerousTransitions = dfs(vector);
    }

    public boolean hasIncorrectFinalState() {
        return dangerousTransitions != null;
    }

    public String getRedIds() {
        if (dangerousTransitions != null) {
            StringBuilder message = new StringBuilder();
            for (Transition transition : dangerousTransitions) {
                message.append(transition.getSource().getId() + ", ");
            }
            message.replace(message.length() - 2, message.length() - 1, "");
            return message.toString();
        }
        return "";
    }

    private List<Transition> dfs(Vector uVector) {
        if (DEBUG) {
            StringBuilder str = new StringBuilder();
            str.append("Current U vector is:");
            str.append("\n");
            str.append(uVector.toString());
            str.append("\n");
            PluginLogger.logInfo(str.toString());
        }

        visited.put(uVector, true);

        for (Vector vVector : vVectorList) {
            Vector tempVector = uVector.getVectorsSum(vVector);

            boolean allZeros = true;
            for (int i = 0; i < tempVector.getElements().length; ++i) {
                if (uVector.getElements()[i] > 0) allZeros = false;
            }
            if (allZeros) return null;
        }

        List<Vector> adjacentList = vectorGraph.getOrDefault(uVector, null);
        if (adjacentList == null) {
            List<Transition> redTransitions = new ArrayList<>();
            for (int i = 0; i < uVector.getElements().length; ++i) {
                if (uVector.getElements()[i] > 0) redTransitions.add(transitions.get(i - 1));
            }
            return redTransitions;
        }

        for (Vector vector : adjacentList) {
            if (!visited.getOrDefault(vector, false)) {
                List<Transition> redTransitions = dfs(vector);
                if (redTransitions != null) return redTransitions;
            }
        }
        return null;
    }

    private void populateVectorList() {
        for (Node node : nodes) {
            if (node instanceof StartState) {
                for (Transition transition : transitions) {
                    if (transition.getSource().equals(node)) {
                        Vector v = new Vector(transitions.size() + 1);
                        v.setElementValue(0, -1);
                        v.setElementValue(transitions.indexOf(transition) + 1, 1);
                        vVectorList.add(v);
                    }
                }
            }
        }

        for (Node node : nodes) {
            if (node instanceof Join || node instanceof Fork || node instanceof ParallelGateway) {
                Vector v = new Vector(transitions.size() + 1);
                for (Transition transition : transitions) {
                    if (transition.getSource().equals(node)) {
                        v.setElementValue(transitions.indexOf(transition) + 1, 1);
                    }
                    if (transition.getTarget().equals(node)) {
                        v.setElementValue(transitions.indexOf(transition) + 1, -1);
                    }
                }

                vVectorList.add(v);
            }
        }

        for (Node node : nodes) {
            if (!(node instanceof Join || node instanceof Fork || node instanceof ParallelGateway || node instanceof StartState || node instanceof EndState)) {
                for (Transition transition : transitions) {
                    if (transition.getTarget().equals(node)) {
                        List<Transition> addedVectors = new ArrayList<Transition>();
                        for (Transition transition1 : transitions) {
                            Node sourceNode = transition1.getSource();
                            if (sourceNode instanceof Timer && sourceNode.getParent() instanceof Node) {
                                sourceNode = (Node) sourceNode.getParent();
                            }
                            if (sourceNode.equals(node) && !addedVectors.contains(transition1)) {
                                Vector v = new Vector(transitions.size() + 1);
                                v.setElementValue(transitions.indexOf(transition) + 1, -1);
                                v.setElementValue(transitions.indexOf(transition1) + 1, 1);
                                vVectorList.add(v);
                                addedVectors.add(transition1);
                            }
                        }
                    }
                }
            }
        }
    }

    private List<Vector> getAttainableVectorList(Vector unprocessedVector) {
        List<Vector> buffer = new ArrayList<Vector>();
        List<Vector> listVectors = new ArrayList<Vector>();

        for (TransitionVector transitionVector : transitionVectors) {
            if (Arrays.equals(unprocessedVector.getElements(), transitionVector.getToVector().getElements())) {
                buffer.add(transitionVector.getFromVector());
            }
        }

        while (buffer.size() > 0) {
            List<Vector> foundedVectors = new ArrayList<Vector>();
            for (TransitionVector transitionVector : transitionVectors) {
                for (Vector tempVector : buffer) {
                    if (Arrays.equals(tempVector.getElements(), transitionVector.getToVector().getElements())) {
                        foundedVectors.add(transitionVector.getFromVector());
                    }
                }
            }

            Iterator<Vector> foundedIterator = foundedVectors.iterator();
            while (foundedIterator.hasNext()) {
                Vector foundVector = foundedIterator.next();
                for (Vector bufferVector : buffer) {
                    if (Arrays.equals(foundVector.getElements(), bufferVector.getElements())) {
                        foundedIterator.remove();
                        break;
                    }
                }
            }

            foundedIterator = foundedVectors.iterator();
            while (foundedIterator.hasNext()) {
                Vector foundVector = foundedIterator.next();
                for (Vector listVector : listVectors) {
                    if (Arrays.equals(foundVector.getElements(), listVector.getElements())) {
                        foundedIterator.remove();
                        break;
                    }
                }
            }

            listVectors.addAll(buffer);
            buffer.clear();
            buffer.addAll(foundedVectors);
        }

        return listVectors;
    }
}
