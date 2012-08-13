// This file is part of Notepad++ project
// Copyright (C)2003 Don HO <don.h@free.fr>
//
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either
// version 2 of the License, or (at your option) any later version.
//
// Note that the GPL places important restrictions on "derived works", yet
// it does not provide a detailed definition of that term.  To avoid      
// misunderstandings, we consider an application to constitute a          
// "derivative work" for the purpose of this license if it does any of the
// following:                                                             
// 1. Integrates source code from Notepad++.
// 2. Integrates/includes/aggregates Notepad++ into a proprietary executable
//    installer, such as those produced by InstallShield.
// 3. Links to a library or executes a program that does any of the above.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.


#ifndef ABOUT_DLG_H
#define ABOUT_DLG_H

#ifndef URLCTRL_INCLUDED
#include "URLCtrl.h"
#endif// URLCTRL_INCLUDED

#ifndef RESOURCE_H
#include "resource.h"
#endif// RESOURCE_H

#define LICENCE_TXT \
TEXT("This program is free software; you can redistribute it and/or \
modify it under the terms of the GNU General Public License \
as published by the Free Software Foundation; either \
version 2 of the License, or (at your option) any later version.\r\n\
\r\n\
This program is distributed in the hope that it will be useful, \
but WITHOUT ANY WARRANTY; without even the implied warranty of \
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the \
GNU General Public License for more details. \r\n\
\r\n\
You should have received a copy of the GNU General Public License \
along with this program; if not, write to the Free Software \
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.")



class AboutDlg : public StaticDialog
{
public :
	AboutDlg() : StaticDialog() {};

	void doDialog();

    virtual void destroy() {
        _emailLink.destroy();
        _pageLink.destroy();
    };

protected :
	virtual BOOL CALLBACK run_dlgProc(UINT message, WPARAM wParam, LPARAM lParam);

private :
    URLCtrl _emailLink;
    URLCtrl _pageLink;
};

#endif //ABOUT_DLG_H
