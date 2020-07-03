package ru.runa.gpd.ui.wizard;

import com.google.common.collect.Lists;
import java.io.ByteArrayOutputStream;
import java.io.FileOutputStream;
import java.util.List;
import java.util.ListIterator;
import java.util.TreeMap;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.IStructuredSelection;
import ru.runa.gpd.BotCache;
import ru.runa.gpd.Localization;
import ru.runa.gpd.PluginLogger;
import ru.runa.gpd.bot.BotDeployCommand;
import ru.runa.gpd.bot.BotExportCommand;
import ru.runa.gpd.lang.model.BotTask;
import ru.runa.gpd.ui.custom.Dialogs;
import ru.runa.gpd.ui.enhancement.DialogEnhancement;
import ru.runa.gpd.ui.enhancement.DocxDialogEnhancementMode;
import ru.runa.gpd.util.IOUtils;

public class ExportBotWizardPage extends ExportBotElementWizardPage {
    public ExportBotWizardPage(IStructuredSelection selection) {
        super(selection);
        setTitle(Localization.getString("ExportBotWizardPage.page.title"));
        setDescription(Localization.getString("ExportBotWizardPage.page.description"));
        this.exportObjectNameFileMap = new TreeMap<String, IResource>();
        for (IFolder resource : IOUtils.getAllBotFolders()) {
            exportObjectNameFileMap.put(getKey(resource.getProject(), resource), resource);
        }
    }

    @Override
    protected String getOutputSuffix() {
        return ".bot";
    }

    @Override
    protected String getSelectionResourceKey(IResource resource) {
        return getKey(resource.getProject(), resource);
    }

    @Override
    protected void exportToZipFile(IResource exportResource) throws Exception {
        String errorsDetails[] = { "" };
        if (checkBotTaskParametersWithDocxTemplate(errorsDetails)
                || Dialogs.confirm(Localization.getString("DialogEnhancement.parametersNotCorrespondingWithDocxQ"), errorsDetails[0])) {
            getContainer().run(true, true, new BotExportCommand(exportResource, new FileOutputStream(getDestinationValue())));
            PluginLogger.logInfo(Localization.getString("DialogEnhancement.exportSuccessful"));
        } else {
            PluginLogger.logErrorWithoutDialog(Localization.getString("DialogEnhancement.exportCanceled"));
        }
    }

    @Override
    protected void deployToServer(IResource exportResource) throws Exception {
        String errorsDetails[] = { "" };
        if (!checkBotTaskParametersWithDocxTemplate(errorsDetails)) {
            Dialogs.error(Localization.getString("DialogEnhancement.parametersNotCorrespondingWithDocx"), errorsDetails[0]);
            PluginLogger.logErrorWithoutDialog(Localization.getString("DialogEnhancement.exportCanceled"));
            return;
        }
        getContainer().run(true, true, new BotDeployCommand(exportResource, new ByteArrayOutputStream()));
        PluginLogger.logInfo(Localization.getString("DialogEnhancement.exportSuccessful"));
    }

    private boolean checkBotTaskParametersWithDocxTemplate(String errorsDetails[]) {
        boolean ok = true;
        if (isDialogEnhancementMode() && null != exportResource && exportResource instanceof IFolder) {
            IFolder processDefinitionFolder = (IFolder) exportResource;
            List<BotTask> botTaskList = BotCache.getBotTasks(processDefinitionFolder.getName());
            ListIterator<BotTask> botTaskListIterator = botTaskList.listIterator();
            while (botTaskListIterator.hasNext()) {
                BotTask botTask = botTaskListIterator.next();
                if (!botTask.getDelegationClassName().equals(DocxDialogEnhancementMode.DocxHandlerID)) {
                    continue;
                }
                Object obj = DialogEnhancement.getConfigurationValue(botTask, DocxDialogEnhancementMode.InputPathId);
                String embeddedDocxTemplateFileName = null != obj && obj instanceof String ? (String) obj : "";
                List<String> errors = Lists.newArrayList();
                Boolean result = DialogEnhancement.checkBotTaskParametersWithDocxTemplate(botTask, embeddedDocxTemplateFileName, errors,
                        errorsDetails);
                if (errors.size() > 0) {
                    BotTask.logErrors(BotCache.getBotTaskFile(botTask), errors);
                }
                if (null == result || !result) {
                    ok = false;
                }
            }
        }
        return ok;
    }

    private boolean isDialogEnhancementMode() {
        return DialogEnhancement.isOn();
    }
}
